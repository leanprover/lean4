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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0;
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(lean_object* v_k_71_, lean_object* v___y_72_, lean_object* v_b_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed(lean_object* v_k_80_, lean_object* v___y_81_, lean_object* v_b_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0(v_k_80_, v___y_81_, v_b_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_81_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(lean_object* v_name_89_, uint8_t v_bi_90_, lean_object* v_type_91_, lean_object* v_k_92_, uint8_t v_kind_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; 
lean_inc(v___y_94_);
v___f_100_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___lam__0___boxed), 8, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg___boxed(lean_object* v_name_110_, lean_object* v_bi_111_, lean_object* v_type_112_, lean_object* v_k_113_, lean_object* v_kind_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_bi_boxed_121_; uint8_t v_kind_boxed_122_; lean_object* v_res_123_; 
v_bi_boxed_121_ = lean_unbox(v_bi_111_);
v_kind_boxed_122_ = lean_unbox(v_kind_114_);
v_res_123_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_110_, v_bi_boxed_121_, v_type_112_, v_k_113_, v_kind_boxed_122_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(lean_object* v_00_u03b1_124_, lean_object* v_name_125_, uint8_t v_bi_126_, lean_object* v_type_127_, lean_object* v_k_128_, uint8_t v_kind_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_name_125_, v_bi_126_, v_type_127_, v_k_128_, v_kind_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___boxed(lean_object* v_00_u03b1_137_, lean_object* v_name_138_, lean_object* v_bi_139_, lean_object* v_type_140_, lean_object* v_k_141_, lean_object* v_kind_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_bi_boxed_149_; uint8_t v_kind_boxed_150_; lean_object* v_res_151_; 
v_bi_boxed_149_ = lean_unbox(v_bi_139_);
v_kind_boxed_150_ = lean_unbox(v_kind_142_);
v_res_151_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5(v_00_u03b1_137_, v_name_138_, v_bi_boxed_149_, v_type_140_, v_k_141_, v_kind_boxed_150_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; lean_object* v_env_159_; lean_object* v___x_160_; lean_object* v_mctx_161_; lean_object* v_lctx_162_; lean_object* v_options_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_158_ = lean_st_ref_get(v___y_156_);
v_env_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_159_);
lean_dec(v___x_158_);
v___x_160_ = lean_st_ref_get(v___y_154_);
v_mctx_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc_ref(v_mctx_161_);
lean_dec(v___x_160_);
v_lctx_162_ = lean_ctor_get(v___y_153_, 2);
v_options_163_ = lean_ctor_get(v___y_155_, 2);
lean_inc_ref(v_options_163_);
lean_inc_ref(v_lctx_162_);
v___x_164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_164_, 0, v_env_159_);
lean_ctor_set(v___x_164_, 1, v_mctx_161_);
lean_ctor_set(v___x_164_, 2, v_lctx_162_);
lean_ctor_set(v___x_164_, 3, v_options_163_);
v___x_165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_msgData_152_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0___boxed(lean_object* v_msgData_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msgData_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_ref_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_ref_180_ = lean_ctor_get(v___y_177_, 5);
v___x_181_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_inc(v_ref_180_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_ref_180_);
lean_ctor_set(v___x_186_, 1, v_a_182_);
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 1);
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg___boxed(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
else
{
lean_object* v_key_201_; lean_object* v_tail_202_; uint8_t v___x_203_; 
v_key_201_ = lean_ctor_get(v_x_199_, 0);
v_tail_202_ = lean_ctor_get(v_x_199_, 2);
v___x_203_ = lean_expr_eqv(v_key_201_, v_a_198_);
if (v___x_203_ == 0)
{
v_x_199_ = v_tail_202_;
goto _start;
}
else
{
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg___boxed(lean_object* v_a_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_205_, v_x_206_);
lean_dec(v_x_206_);
lean_dec_ref(v_a_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_key_211_; lean_object* v_value_212_; lean_object* v_tail_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_236_; 
v_key_211_ = lean_ctor_get(v_x_210_, 0);
v_value_212_ = lean_ctor_get(v_x_210_, 1);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_236_ == 0)
{
v___x_215_ = v_x_210_;
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_tail_213_);
lean_inc(v_value_212_);
lean_inc(v_key_211_);
lean_dec(v_x_210_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v_fold_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_217_ = lean_array_get_size(v_x_209_);
v___x_218_ = l_Lean_Expr_hash(v_key_211_);
v___x_219_ = 32ULL;
v___x_220_ = lean_uint64_shift_right(v___x_218_, v___x_219_);
v_fold_221_ = lean_uint64_xor(v___x_218_, v___x_220_);
v___x_222_ = 16ULL;
v___x_223_ = lean_uint64_shift_right(v_fold_221_, v___x_222_);
v___x_224_ = lean_uint64_xor(v_fold_221_, v___x_223_);
v___x_225_ = lean_uint64_to_usize(v___x_224_);
v___x_226_ = lean_usize_of_nat(v___x_217_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_sub(v___x_226_, v___x_227_);
v___x_229_ = lean_usize_land(v___x_225_, v___x_228_);
v___x_230_ = lean_array_uget_borrowed(v_x_209_, v___x_229_);
lean_inc(v___x_230_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 2, v___x_230_);
v___x_232_ = v___x_215_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_key_211_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_value_212_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v___x_230_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = lean_array_uset(v_x_209_, v___x_229_, v___x_232_);
v_x_209_ = v___x_233_;
v_x_210_ = v_tail_213_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(lean_object* v_i_237_, lean_object* v_source_238_, lean_object* v_target_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_array_get_size(v_source_238_);
v___x_241_ = lean_nat_dec_lt(v_i_237_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_source_238_);
lean_dec(v_i_237_);
return v_target_239_;
}
else
{
lean_object* v_es_242_; lean_object* v___x_243_; lean_object* v_source_244_; lean_object* v_target_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_es_242_ = lean_array_fget(v_source_238_, v_i_237_);
v___x_243_ = lean_box(0);
v_source_244_ = lean_array_fset(v_source_238_, v_i_237_, v___x_243_);
v_target_245_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_target_239_, v_es_242_);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_i_237_, v___x_246_);
lean_dec(v_i_237_);
v_i_237_ = v___x_247_;
v_source_238_ = v_source_244_;
v_target_239_ = v_target_245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(lean_object* v_data_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_nbuckets_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_250_ = lean_array_get_size(v_data_249_);
v___x_251_ = lean_unsigned_to_nat(2u);
v_nbuckets_252_ = lean_nat_mul(v___x_250_, v___x_251_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_box(0);
v___x_255_ = lean_mk_array(v_nbuckets_252_, v___x_254_);
v___x_256_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_253_, v_data_249_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object* v_a_257_, lean_object* v_b_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_dec(v_b_258_);
lean_dec_ref(v_a_257_);
return v_x_259_;
}
else
{
lean_object* v_key_260_; lean_object* v_value_261_; lean_object* v_tail_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_274_; 
v_key_260_ = lean_ctor_get(v_x_259_, 0);
v_value_261_ = lean_ctor_get(v_x_259_, 1);
v_tail_262_ = lean_ctor_get(v_x_259_, 2);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_274_ == 0)
{
v___x_264_ = v_x_259_;
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_tail_262_);
lean_inc(v_value_261_);
lean_inc(v_key_260_);
lean_dec(v_x_259_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_274_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
uint8_t v___x_266_; 
v___x_266_ = lean_expr_eqv(v_key_260_, v_a_257_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_257_, v_b_258_, v_tail_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 2, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_key_260_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_value_261_);
lean_ctor_set(v_reuseFailAlloc_270_, 2, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v_value_261_);
lean_dec(v_key_260_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v_b_258_);
lean_ctor_set(v___x_264_, 0, v_a_257_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_257_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_b_258_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_tail_262_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_275_, lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
lean_object* v_size_278_; lean_object* v_buckets_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_322_; 
v_size_278_ = lean_ctor_get(v_m_275_, 0);
v_buckets_279_ = lean_ctor_get(v_m_275_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_m_275_);
if (v_isSharedCheck_322_ == 0)
{
v___x_281_ = v_m_275_;
v_isShared_282_ = v_isSharedCheck_322_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_buckets_279_);
lean_inc(v_size_278_);
lean_dec(v_m_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_322_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v_fold_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v_bkt_296_; uint8_t v___x_297_; 
v___x_283_ = lean_array_get_size(v_buckets_279_);
v___x_284_ = l_Lean_Expr_hash(v_a_276_);
v___x_285_ = 32ULL;
v___x_286_ = lean_uint64_shift_right(v___x_284_, v___x_285_);
v_fold_287_ = lean_uint64_xor(v___x_284_, v___x_286_);
v___x_288_ = 16ULL;
v___x_289_ = lean_uint64_shift_right(v_fold_287_, v___x_288_);
v___x_290_ = lean_uint64_xor(v_fold_287_, v___x_289_);
v___x_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = lean_usize_of_nat(v___x_283_);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_sub(v___x_292_, v___x_293_);
v___x_295_ = lean_usize_land(v___x_291_, v___x_294_);
v_bkt_296_ = lean_array_uget_borrowed(v_buckets_279_, v___x_295_);
v___x_297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_276_, v_bkt_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v_size_x27_299_; lean_object* v___x_300_; lean_object* v_buckets_x27_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v_size_x27_299_ = lean_nat_add(v_size_278_, v___x_298_);
lean_dec(v_size_278_);
lean_inc(v_bkt_296_);
v___x_300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_300_, 0, v_a_276_);
lean_ctor_set(v___x_300_, 1, v_b_277_);
lean_ctor_set(v___x_300_, 2, v_bkt_296_);
v_buckets_x27_301_ = lean_array_uset(v_buckets_279_, v___x_295_, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(4u);
v___x_303_ = lean_nat_mul(v_size_x27_299_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(3u);
v___x_305_ = lean_nat_div(v___x_303_, v___x_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_array_get_size(v_buckets_x27_301_);
v___x_307_ = lean_nat_dec_le(v___x_305_, v___x_306_);
lean_dec(v___x_305_);
if (v___x_307_ == 0)
{
lean_object* v_val_308_; lean_object* v___x_310_; 
v_val_308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_301_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_val_308_);
lean_ctor_set(v___x_281_, 0, v_size_x27_299_);
v___x_310_ = v___x_281_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_size_x27_299_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_val_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
lean_object* v___x_313_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_buckets_x27_301_);
lean_ctor_set(v___x_281_, 0, v_size_x27_299_);
v___x_313_ = v___x_281_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_size_x27_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_buckets_x27_301_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v_buckets_x27_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_inc(v_bkt_296_);
v___x_315_ = lean_box(0);
v_buckets_x27_316_ = lean_array_uset(v_buckets_279_, v___x_295_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_276_, v_b_277_, v_bkt_296_);
v___x_318_ = lean_array_uset(v_buckets_x27_316_, v___x_295_, v___x_317_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_318_);
v___x_320_ = v___x_281_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_278_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object* v_a_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v_key_326_; lean_object* v_value_327_; lean_object* v_tail_328_; uint8_t v___x_329_; 
v_key_326_ = lean_ctor_get(v_x_324_, 0);
v_value_327_ = lean_ctor_get(v_x_324_, 1);
v_tail_328_ = lean_ctor_get(v_x_324_, 2);
v___x_329_ = lean_expr_eqv(v_key_326_, v_a_323_);
if (v___x_329_ == 0)
{
v_x_324_ = v_tail_328_;
goto _start;
}
else
{
lean_object* v___x_331_; 
lean_inc(v_value_327_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v_value_327_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_buckets_337_; lean_object* v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_buckets_337_ = lean_ctor_get(v_m_335_, 1);
v___x_338_ = lean_array_get_size(v_buckets_337_);
v___x_339_ = l_Lean_Expr_hash(v_a_336_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_338_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v___x_351_ = lean_array_uget_borrowed(v_buckets_337_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_336_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_353_, v_a_354_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_m_353_);
return v_res_355_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_356_; lean_object* v_dummy_357_; 
v___x_356_ = lean_box(0);
v_dummy_357_ = l_Lean_Expr_sort___override(v___x_356_);
return v_dummy_357_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_args_361_, lean_object* v_a_362_, lean_object* v_snd_363_, lean_object* v_____r_364_, lean_object* v_fty_365_, lean_object* v_j_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
if (lean_obj_tag(v_fty_365_) == 7)
{
lean_object* v_body_373_; uint8_t v_binderInfo_374_; lean_object* v___x_375_; uint8_t v_a_377_; uint8_t v___x_424_; 
v_body_373_ = lean_ctor_get(v_fty_365_, 2);
lean_inc_ref(v_body_373_);
v_binderInfo_374_ = lean_ctor_get_uint8(v_fty_365_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_365_, 3);
v___x_375_ = lean_array_fget_borrowed(v_args_361_, v_a_362_);
v___x_424_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_374_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Lean_Expr_isSort(v___x_375_);
v___x_426_ = lean_bool_not(v___x_425_);
if (v___x_426_ == 0)
{
v_a_377_ = v___x_426_;
goto v___jp_376_;
}
else
{
lean_object* v___x_427_; 
lean_inc(v___x_375_);
v___x_427_ = l_Lean_Meta_isTypeFormer(v___x_375_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; uint8_t v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = lean_unbox(v_a_428_);
lean_dec(v_a_428_);
v_a_377_ = v___x_429_;
goto v___jp_376_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_body_373_);
lean_dec(v_snd_363_);
v_a_430_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_427_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
else
{
v_a_377_ = v___x_424_;
goto v___jp_376_;
}
v___jp_376_:
{
if (v_a_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_inc(v_j_366_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_j_366_);
lean_ctor_set(v___x_378_, 1, v_snd_363_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_body_373_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
lean_inc(v___x_375_);
v___x_382_ = l_Lean_Meta_isProof(v___x_375_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_415_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_415_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_415_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_415_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v_a_383_);
lean_dec(v_a_383_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_del_object(v___x_385_);
lean_inc(v___x_375_);
v___x_388_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_375_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_400_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_400_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_400_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_393_ = l_Lean_Expr_app___override(v_snd_363_, v_a_389_);
lean_inc(v_j_366_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_j_366_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_body_373_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_396_);
v___x_398_ = v___x_391_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_body_373_);
lean_dec(v_snd_363_);
v_a_401_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_388_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_388_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_j_366_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_j_366_);
lean_ctor_set(v___x_409_, 1, v_snd_363_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_body_373_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_411_);
v___x_413_ = v___x_385_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v_body_373_);
lean_dec(v_snd_363_);
v_a_416_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_382_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_382_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_439_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_438_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_439_, 0);
lean_dec(v_unused_450_);
v___x_441_ = v___x_439_;
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
else
{
lean_dec(v___x_439_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_449_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
lean_inc(v_j_366_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_j_366_);
lean_ctor_set(v___x_443_, 1, v_snd_363_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_fty_365_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_fty_365_);
lean_dec(v_snd_363_);
v_a_451_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_439_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_439_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_459_; uint64_t v___x_460_; 
v___x_459_ = 0;
v___x_460_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_461_, lean_object* v_args_462_, lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___y_472_; uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_lt(v_a_463_, v_upperBound_461_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_a_463_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_b_464_);
return v___x_495_;
}
else
{
lean_object* v_snd_496_; lean_object* v_fst_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v_a_501_; uint8_t v___x_504_; 
v_snd_496_ = lean_ctor_get(v_b_464_, 1);
lean_inc(v_snd_496_);
v_fst_497_ = lean_ctor_get(v_b_464_, 0);
lean_inc(v_fst_497_);
lean_dec_ref(v_b_464_);
v_fst_498_ = lean_ctor_get(v_snd_496_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_snd_496_, 1);
lean_inc(v_snd_499_);
lean_dec(v_snd_496_);
v___x_504_ = l_Lean_Expr_isForall(v_fst_497_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v_foApprox_506_; uint8_t v_ctxApprox_507_; uint8_t v_quasiPatternApprox_508_; uint8_t v_constApprox_509_; uint8_t v_isDefEqStuckEx_510_; uint8_t v_unificationHints_511_; uint8_t v_proofIrrelevance_512_; uint8_t v_assignSyntheticOpaque_513_; uint8_t v_offsetCnstrs_514_; uint8_t v_etaStruct_515_; uint8_t v_univApprox_516_; uint8_t v_iota_517_; uint8_t v_beta_518_; uint8_t v_proj_519_; uint8_t v_zeta_520_; uint8_t v_zetaDelta_521_; uint8_t v_zetaUnused_522_; uint8_t v_zetaHave_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_561_; 
v___x_505_ = l_Lean_Meta_Context_config(v___y_466_);
v_foApprox_506_ = lean_ctor_get_uint8(v___x_505_, 0);
v_ctxApprox_507_ = lean_ctor_get_uint8(v___x_505_, 1);
v_quasiPatternApprox_508_ = lean_ctor_get_uint8(v___x_505_, 2);
v_constApprox_509_ = lean_ctor_get_uint8(v___x_505_, 3);
v_isDefEqStuckEx_510_ = lean_ctor_get_uint8(v___x_505_, 4);
v_unificationHints_511_ = lean_ctor_get_uint8(v___x_505_, 5);
v_proofIrrelevance_512_ = lean_ctor_get_uint8(v___x_505_, 6);
v_assignSyntheticOpaque_513_ = lean_ctor_get_uint8(v___x_505_, 7);
v_offsetCnstrs_514_ = lean_ctor_get_uint8(v___x_505_, 8);
v_etaStruct_515_ = lean_ctor_get_uint8(v___x_505_, 10);
v_univApprox_516_ = lean_ctor_get_uint8(v___x_505_, 11);
v_iota_517_ = lean_ctor_get_uint8(v___x_505_, 12);
v_beta_518_ = lean_ctor_get_uint8(v___x_505_, 13);
v_proj_519_ = lean_ctor_get_uint8(v___x_505_, 14);
v_zeta_520_ = lean_ctor_get_uint8(v___x_505_, 15);
v_zetaDelta_521_ = lean_ctor_get_uint8(v___x_505_, 16);
v_zetaUnused_522_ = lean_ctor_get_uint8(v___x_505_, 17);
v_zetaHave_523_ = lean_ctor_get_uint8(v___x_505_, 18);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_561_ == 0)
{
v___x_525_ = v___x_505_;
v_isShared_526_ = v_isSharedCheck_561_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_505_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_561_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
uint8_t v_trackZetaDelta_527_; lean_object* v_zetaDeltaSet_528_; lean_object* v_lctx_529_; lean_object* v_localInstances_530_; lean_object* v_defEqCtx_x3f_531_; lean_object* v_synthPendingDepth_532_; lean_object* v_canUnfold_x3f_533_; uint8_t v_univApprox_534_; uint8_t v_inTypeClassResolution_535_; uint8_t v_cacheInferType_536_; uint8_t v___x_537_; lean_object* v_config_539_; 
v_trackZetaDelta_527_ = lean_ctor_get_uint8(v___y_466_, sizeof(void*)*7);
v_zetaDeltaSet_528_ = lean_ctor_get(v___y_466_, 1);
v_lctx_529_ = lean_ctor_get(v___y_466_, 2);
v_localInstances_530_ = lean_ctor_get(v___y_466_, 3);
v_defEqCtx_x3f_531_ = lean_ctor_get(v___y_466_, 4);
v_synthPendingDepth_532_ = lean_ctor_get(v___y_466_, 5);
v_canUnfold_x3f_533_ = lean_ctor_get(v___y_466_, 6);
v_univApprox_534_ = lean_ctor_get_uint8(v___y_466_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_535_ = lean_ctor_get_uint8(v___y_466_, sizeof(void*)*7 + 2);
v_cacheInferType_536_ = lean_ctor_get_uint8(v___y_466_, sizeof(void*)*7 + 3);
v___x_537_ = 0;
if (v_isShared_526_ == 0)
{
v_config_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 0, v_foApprox_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 1, v_ctxApprox_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 2, v_quasiPatternApprox_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 3, v_constApprox_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 4, v_isDefEqStuckEx_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 5, v_unificationHints_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 6, v_proofIrrelevance_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 7, v_assignSyntheticOpaque_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 8, v_offsetCnstrs_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 10, v_etaStruct_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 11, v_univApprox_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 12, v_iota_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 13, v_beta_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 14, v_proj_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 15, v_zeta_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 16, v_zetaDelta_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 17, v_zetaUnused_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, 18, v_zetaHave_523_);
v_config_539_ = v_reuseFailAlloc_560_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; lean_object* v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v_key_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_ctor_set_uint8(v_config_539_, 9, v___x_537_);
v___x_540_ = l_Lean_Meta_Context_configKey(v___y_466_);
v___x_541_ = 3ULL;
v___x_542_ = lean_uint64_shift_right(v___x_540_, v___x_541_);
v___x_543_ = lean_expr_instantiate_rev_range(v_fst_497_, v_fst_498_, v_a_463_, v_args_462_);
lean_dec(v_fst_498_);
lean_dec(v_fst_497_);
v___x_544_ = lean_uint64_shift_left(v___x_542_, v___x_541_);
v___x_545_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___closed__0);
v_key_546_ = lean_uint64_lor(v___x_544_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_547_, 0, v_config_539_);
lean_ctor_set_uint64(v___x_547_, sizeof(void*)*1, v_key_546_);
lean_inc(v_canUnfold_x3f_533_);
lean_inc(v_synthPendingDepth_532_);
lean_inc(v_defEqCtx_x3f_531_);
lean_inc_ref(v_localInstances_530_);
lean_inc_ref(v_lctx_529_);
lean_inc(v_zetaDeltaSet_528_);
v___x_548_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_zetaDeltaSet_528_);
lean_ctor_set(v___x_548_, 2, v_lctx_529_);
lean_ctor_set(v___x_548_, 3, v_localInstances_530_);
lean_ctor_set(v___x_548_, 4, v_defEqCtx_x3f_531_);
lean_ctor_set(v___x_548_, 5, v_synthPendingDepth_532_);
lean_ctor_set(v___x_548_, 6, v_canUnfold_x3f_533_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*7, v_trackZetaDelta_527_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*7 + 1, v_univApprox_534_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*7 + 2, v_inTypeClassResolution_535_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*7 + 3, v_cacheInferType_536_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v___y_467_);
v___x_549_ = lean_whnf(v___x_543_, v___x_548_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v_a_501_ = v_a_550_;
goto v___jp_500_;
}
else
{
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_549_, 1);
v_a_501_ = v_a_551_;
goto v___jp_500_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_snd_499_);
lean_dec(v_a_463_);
v_a_552_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_549_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(0);
v___x_563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_462_, v_a_463_, v_snd_499_, v___x_562_, v_fst_497_, v_fst_498_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v_fst_498_);
v___y_472_ = v___x_563_;
goto v___jp_471_;
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(0);
v___x_503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_462_, v_a_463_, v_snd_499_, v___x_502_, v_a_501_, v_a_463_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
v___y_472_ = v___x_503_;
goto v___jp_471_;
}
}
v___jp_471_:
{
if (lean_obj_tag(v___y_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_a_473_ = lean_ctor_get(v___y_472_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v___y_472_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___y_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
if (lean_obj_tag(v_a_473_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; 
lean_dec(v_a_463_);
v_a_477_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v_a_473_, 1);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_a_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_del_object(v___x_475_);
v_a_481_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_a_473_, 1);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_a_463_, v___x_482_);
lean_dec(v_a_463_);
v_a_463_ = v___x_483_;
v_b_464_ = v_a_481_;
goto _start;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_a_463_);
v_a_486_ = lean_ctor_get(v___y_472_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___y_472_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___y_472_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_x_564_) == 5)
{
lean_object* v_fn_573_; lean_object* v_arg_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_fn_573_ = lean_ctor_get(v_x_564_, 0);
lean_inc_ref(v_fn_573_);
v_arg_574_ = lean_ctor_get(v_x_564_, 1);
lean_inc_ref(v_arg_574_);
lean_dec_ref_known(v_x_564_, 2);
v___x_575_ = lean_array_set(v_x_565_, v_x_566_, v_arg_574_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v_x_566_, v___x_576_);
lean_dec(v_x_566_);
v_x_564_ = v_fn_573_;
v_x_565_ = v___x_575_;
v_x_566_ = v___x_577_;
goto _start;
}
else
{
lean_object* v___x_579_; 
lean_dec(v_x_566_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc_ref(v_x_564_);
v___x_579_ = lean_infer_type(v_x_564_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_564_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_array_get_size(v_x_565_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_582_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_a_580_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_583_, v_x_565_, v___x_584_, v___x_586_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec_ref(v_x_565_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_597_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_597_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_snd_592_; lean_object* v_snd_593_; lean_object* v___x_595_; 
v_snd_592_ = lean_ctor_get(v_a_588_, 1);
lean_inc(v_snd_592_);
lean_dec(v_a_588_);
v_snd_593_ = lean_ctor_get(v_snd_592_, 1);
lean_inc(v_snd_593_);
lean_dec(v_snd_592_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_snd_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_snd_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_587_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_587_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_dec(v_a_580_);
lean_dec_ref(v_x_565_);
return v___x_581_;
}
}
else
{
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_564_);
return v___x_579_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Lean_Expr_bvar___override(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_608_, lean_object* v_binderName_609_, uint8_t v_binderInfo_610_, lean_object* v_binderType_611_, lean_object* v_arg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_ty_x27_620_; uint8_t v___x_632_; 
v___x_632_ = l_Lean_Expr_hasLooseBVars(v_body_608_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_611_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v_ty_x27_620_ = v_a_634_;
goto v___jp_619_;
}
else
{
lean_dec(v_binderName_609_);
return v___x_633_;
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_binderType_611_);
v___x_635_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_620_ = v___x_635_;
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_expr_instantiate1(v_body_608_, v_arg_612_);
v___x_622_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_621_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = l_Lean_Expr_forallE___override(v_binderName_609_, v_ty_x27_620_, v_a_623_, v_binderInfo_610_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_dec_ref(v_ty_x27_620_);
lean_dec(v_binderName_609_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_636_, lean_object* v_binderName_637_, lean_object* v_binderInfo_638_, lean_object* v_binderType_639_, lean_object* v_arg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
uint8_t v_binderInfo_18508__boxed_647_; lean_object* v_res_648_; 
v_binderInfo_18508__boxed_647_ = lean_unbox(v_binderInfo_638_);
v_res_648_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_636_, v_binderName_637_, v_binderInfo_18508__boxed_647_, v_binderType_639_, v_arg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_body_636_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_649_, lean_object* v_arg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_649_, v_arg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v_arg_650_);
lean_dec_ref(v_body_649_);
return v_res_657_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_662_ = l_Lean_Level_param___override(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_664_ = l_Lean_Expr_sort___override(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_Level_succ___override(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_668_ = l_Lean_Expr_sort___override(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_a_677_; lean_object* v___y_683_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_st_ref_get(v_a_670_);
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_685_, v_e_669_);
lean_dec(v___x_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v___x_687_; 
lean_inc_ref(v_e_669_);
v___x_687_ = l_Lean_Meta_isProof(v_e_669_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; uint8_t v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = lean_unbox(v_a_688_);
lean_dec(v_a_688_);
if (v___x_689_ == 0)
{
switch(lean_obj_tag(v_e_669_))
{
case 5:
{
lean_object* v___x_690_; 
v___x_690_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_669_, v_a_674_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
if (lean_obj_tag(v_a_691_) == 1)
{
lean_object* v_val_692_; lean_object* v___x_693_; 
v_val_692_ = lean_ctor_get(v_a_691_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_a_691_, 1);
v___x_693_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_692_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_693_;
goto v___jp_682_;
}
else
{
lean_object* v_dummy_694_; lean_object* v_nargs_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_a_691_);
v_dummy_694_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_695_ = l_Lean_Expr_getAppNumArgs(v_e_669_);
lean_inc(v_nargs_695_);
v___x_696_ = lean_mk_array(v_nargs_695_, v_dummy_694_);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_sub(v_nargs_695_, v___x_697_);
lean_dec(v_nargs_695_);
lean_inc_ref(v_e_669_);
v___x_699_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_669_, v___x_696_, v___x_698_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref_known(v_e_669_, 2);
v_a_700_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_690_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
case 7:
{
lean_object* v_binderName_708_; lean_object* v_binderType_709_; lean_object* v_body_710_; uint8_t v_binderInfo_711_; lean_object* v___x_712_; lean_object* v___f_713_; uint8_t v___x_714_; lean_object* v___x_715_; 
v_binderName_708_ = lean_ctor_get(v_e_669_, 0);
v_binderType_709_ = lean_ctor_get(v_e_669_, 1);
v_body_710_ = lean_ctor_get(v_e_669_, 2);
v_binderInfo_711_ = lean_ctor_get_uint8(v_e_669_, sizeof(void*)*3 + 8);
v___x_712_ = lean_box(v_binderInfo_711_);
lean_inc_ref_n(v_binderType_709_, 2);
lean_inc_n(v_binderName_708_, 2);
lean_inc_ref(v_body_710_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_713_, 0, v_body_710_);
lean_closure_set(v___f_713_, 1, v_binderName_708_);
lean_closure_set(v___f_713_, 2, v___x_712_);
lean_closure_set(v___f_713_, 3, v_binderType_709_);
v___x_714_ = 0;
v___x_715_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_708_, v_binderInfo_711_, v_binderType_709_, v___f_713_, v___x_714_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_715_;
goto v___jp_682_;
}
case 6:
{
lean_object* v_binderName_716_; lean_object* v_binderType_717_; lean_object* v_body_718_; uint8_t v_binderInfo_719_; lean_object* v___x_720_; 
v_binderName_716_ = lean_ctor_get(v_e_669_, 0);
v_binderType_717_ = lean_ctor_get(v_e_669_, 1);
v_body_718_ = lean_ctor_get(v_e_669_, 2);
v_binderInfo_719_ = lean_ctor_get_uint8(v_e_669_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_669_);
v___x_720_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_669_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_721_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_722_;
goto v___jp_682_;
}
else
{
lean_object* v___f_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
lean_dec(v___x_720_);
lean_inc_ref(v_body_718_);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_723_, 0, v_body_718_);
v___x_724_ = 0;
lean_inc_ref(v_binderType_717_);
lean_inc(v_binderName_716_);
v___x_725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_716_, v_binderInfo_719_, v_binderType_717_, v___f_723_, v___x_724_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_725_;
goto v___jp_682_;
}
}
case 8:
{
lean_object* v_value_726_; lean_object* v_body_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_value_726_ = lean_ctor_get(v_e_669_, 2);
v_body_727_ = lean_ctor_get(v_e_669_, 3);
v___x_728_ = lean_expr_instantiate1(v_body_727_, v_value_726_);
v___x_729_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_728_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_729_;
goto v___jp_682_;
}
case 3:
{
uint8_t v___x_730_; 
v___x_730_ = l_Lean_Expr_isProp(v_e_669_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_Expr_isType(v_e_669_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_677_ = v___x_732_;
goto v___jp_676_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_677_ = v___x_733_;
goto v___jp_676_;
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_677_ = v___x_734_;
goto v___jp_676_;
}
}
case 4:
{
lean_object* v_declName_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_declName_735_ = lean_ctor_get(v_e_669_, 0);
v___x_736_ = lean_box(0);
lean_inc(v_declName_735_);
v___x_737_ = l_Lean_Expr_const___override(v_declName_735_, v___x_736_);
v_a_677_ = v___x_737_;
goto v___jp_676_;
}
case 10:
{
lean_object* v_expr_738_; lean_object* v___x_739_; 
v_expr_738_ = lean_ctor_get(v_e_669_, 1);
lean_inc_ref(v_expr_738_);
v___x_739_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_738_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
v___y_683_ = v___x_739_;
goto v___jp_682_;
}
default: 
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_677_ = v___x_740_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_677_ = v___x_741_;
goto v___jp_676_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_e_669_);
v_a_742_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_687_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_687_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_val_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_e_669_);
v_val_750_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_686_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_val_750_);
lean_dec(v___x_686_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_val_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_st_ref_take(v_a_670_);
lean_inc_ref(v_a_677_);
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_678_, v_e_669_, v_a_677_);
v___x_680_ = lean_st_ref_set(v_a_670_, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_a_677_);
return v___x_681_;
}
v___jp_682_:
{
if (lean_obj_tag(v___y_683_) == 0)
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v___y_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___y_683_, 1);
v_a_677_ = v_a_684_;
goto v___jp_676_;
}
else
{
lean_dec_ref(v_e_669_);
return v___y_683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_758_, lean_object* v_arg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_expr_instantiate1(v_body_758_, v_arg_759_);
v___x_767_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_766_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_768_, v_x_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_778_, lean_object* v_args_779_, lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_778_, v_args_779_, v_a_780_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v_args_779_);
lean_dec(v_upperBound_778_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_args_789_, lean_object* v_a_790_, lean_object* v_snd_791_, lean_object* v_____r_792_, lean_object* v_fty_793_, lean_object* v_j_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_args_789_, v_a_790_, v_snd_791_, v_____r_792_, v_fty_793_, v_j_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v_j_794_);
lean_dec(v_a_790_);
lean_dec_ref(v_args_789_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_810_, lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_818_, lean_object* v_msg_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_818_, v_msg_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_826_, lean_object* v_args_827_, lean_object* v_inst_828_, lean_object* v_R_829_, lean_object* v_a_830_, lean_object* v_b_831_, lean_object* v_c_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_826_, v_args_827_, v_a_830_, v_b_831_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_840_, lean_object* v_args_841_, lean_object* v_inst_842_, lean_object* v_R_843_, lean_object* v_a_844_, lean_object* v_b_845_, lean_object* v_c_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_840_, v_args_841_, v_inst_842_, v_R_843_, v_a_844_, v_b_845_, v_c_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v_args_841_);
lean_dec(v_upperBound_840_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_855_, v_a_856_, v_b_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_859_, lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_860_, v_a_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_863_, lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_863_, v_m_864_, v_a_865_);
lean_dec_ref(v_a_865_);
lean_dec_ref(v_m_864_);
return v_res_866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_867_, lean_object* v_a_868_, lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_871_, lean_object* v_a_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_871_, v_a_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec_ref(v_a_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object* v_00_u03b2_876_, lean_object* v_data_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object* v_00_u03b2_879_, lean_object* v_a_880_, lean_object* v_b_881_, lean_object* v_x_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_880_, v_b_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object* v_00_u03b2_884_, lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_888_, lean_object* v_a_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_888_, v_a_889_, v_x_890_);
lean_dec(v_x_890_);
lean_dec_ref(v_a_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_892_, lean_object* v_i_893_, lean_object* v_source_894_, lean_object* v_target_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_893_, v_source_894_, v_target_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_898_, v_x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
v___x_902_ = lean_unsigned_to_nat(16u);
v___x_903_ = lean_mk_array(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_914_ = lean_st_mk_ref(v___x_913_);
v___x_915_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_907_, v___x_914_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_st_ref_get(v___x_914_);
lean_dec(v___x_914_);
lean_dec(v___x_920_);
if (v_isShared_919_ == 0)
{
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_916_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_dec(v___x_914_);
return v___x_915_;
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_932_, lean_object* v_a_933_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_950_, v_a_951_);
lean_dec_ref(v_a_951_);
lean_dec_ref(v_m_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object* v_m_954_, lean_object* v_a_955_, lean_object* v_b_956_){
_start:
{
lean_object* v_size_957_; lean_object* v_buckets_958_; lean_object* v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v_fold_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v_bkt_972_; uint8_t v___x_973_; 
v_size_957_ = lean_ctor_get(v_m_954_, 0);
v_buckets_958_ = lean_ctor_get(v_m_954_, 1);
v___x_959_ = lean_array_get_size(v_buckets_958_);
v___x_960_ = l_Lean_Expr_hash(v_a_955_);
v___x_961_ = 32ULL;
v___x_962_ = lean_uint64_shift_right(v___x_960_, v___x_961_);
v_fold_963_ = lean_uint64_xor(v___x_960_, v___x_962_);
v___x_964_ = 16ULL;
v___x_965_ = lean_uint64_shift_right(v_fold_963_, v___x_964_);
v___x_966_ = lean_uint64_xor(v_fold_963_, v___x_965_);
v___x_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = lean_usize_of_nat(v___x_959_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_sub(v___x_968_, v___x_969_);
v___x_971_ = lean_usize_land(v___x_967_, v___x_970_);
v_bkt_972_ = lean_array_uget_borrowed(v_buckets_958_, v___x_971_);
v___x_973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_955_, v_bkt_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
lean_inc_ref(v_buckets_958_);
lean_inc(v_size_957_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_m_954_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_995_ = lean_ctor_get(v_m_954_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_m_954_, 0);
lean_dec(v_unused_996_);
v___x_975_ = v_m_954_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_dec(v_m_954_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v_size_x27_978_; lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v_size_x27_978_ = lean_nat_add(v_size_957_, v___x_977_);
lean_dec(v_size_957_);
lean_inc(v_bkt_972_);
v___x_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_979_, 0, v_a_955_);
lean_ctor_set(v___x_979_, 1, v_b_956_);
lean_ctor_set(v___x_979_, 2, v_bkt_972_);
v_buckets_x27_980_ = lean_array_uset(v_buckets_958_, v___x_971_, v___x_979_);
v___x_981_ = lean_unsigned_to_nat(4u);
v___x_982_ = lean_nat_mul(v_size_x27_978_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(3u);
v___x_984_ = lean_nat_div(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_array_get_size(v_buckets_x27_980_);
v___x_986_ = lean_nat_dec_le(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v_val_987_; lean_object* v___x_989_; 
v_val_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_980_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v_val_987_);
lean_ctor_set(v___x_975_, 0, v_size_x27_978_);
v___x_989_ = v___x_975_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_x27_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_val_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_object* v___x_992_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v_buckets_x27_980_);
lean_ctor_set(v___x_975_, 0, v_size_x27_978_);
v___x_992_ = v___x_975_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_size_x27_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_buckets_x27_980_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_dec(v_b_956_);
lean_dec_ref(v_a_955_);
return v_m_954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_1002_, uint8_t v_omitTopForall_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
switch(lean_obj_tag(v_e_1002_))
{
case 4:
{
lean_object* v_declName_1010_; lean_object* v___x_1011_; lean_object* v_seen_1012_; lean_object* v_consts_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1040_; 
v_declName_1010_ = lean_ctor_get(v_e_1002_, 0);
lean_inc(v_declName_1010_);
lean_dec_ref_known(v_e_1002_, 2);
v___x_1011_ = lean_st_ref_take(v_a_1004_);
v_seen_1012_ = lean_ctor_get(v___x_1011_, 0);
v_consts_1013_ = lean_ctor_get(v___x_1011_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1015_ = v___x_1011_;
v_isShared_1016_ = v_isSharedCheck_1040_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_consts_1013_);
lean_inc(v_seen_1012_);
lean_dec(v___x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1040_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_inc(v_declName_1010_);
v___x_1017_ = l_Lean_NameSet_insert(v_consts_1013_, v_declName_1010_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_seen_1012_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_st_ref_set(v_a_1004_, v___x_1019_);
v___x_1021_ = l_Lean_Name_eraseMacroScopes(v_declName_1010_);
lean_dec(v_declName_1010_);
if (lean_obj_tag(v___x_1021_) == 1)
{
lean_object* v_str_1022_; lean_object* v___x_1023_; uint32_t v___x_1024_; uint32_t v___x_1025_; uint8_t v___x_1026_; 
v_str_1022_ = lean_ctor_get(v___x_1021_, 1);
lean_inc_ref(v_str_1022_);
lean_dec_ref_known(v___x_1021_, 2);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_string_utf8_get(v_str_1022_, v___x_1023_);
v___x_1025_ = 97;
v___x_1026_ = lean_uint32_dec_le(v___x_1025_, v___x_1024_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_string_utf8_set(v_str_1022_, v___x_1023_, v___x_1024_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
else
{
uint32_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = 122;
v___x_1030_ = lean_uint32_dec_le(v___x_1024_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_string_utf8_set(v_str_1022_, v___x_1023_, v___x_1024_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
else
{
uint32_t v___x_1033_; uint32_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = 4294967264;
v___x_1034_ = lean_uint32_add(v___x_1024_, v___x_1033_);
v___x_1035_ = lean_string_utf8_set(v_str_1022_, v___x_1023_, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v___x_1021_);
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
}
}
case 5:
{
lean_object* v_fn_1041_; lean_object* v_arg_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_fn_1041_ = lean_ctor_get(v_e_1002_, 0);
lean_inc_ref(v_fn_1041_);
v_arg_1042_ = lean_ctor_get(v_e_1002_, 1);
lean_inc_ref(v_arg_1042_);
lean_dec_ref_known(v_e_1002_, 2);
v___x_1043_ = 0;
v___x_1044_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1041_, v___x_1043_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1042_, v___x_1043_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = lean_string_append(v_a_1045_, v_a_1047_);
lean_dec(v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
case 7:
{
lean_object* v_binderType_1056_; lean_object* v_body_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v_a_1060_; 
v_binderType_1056_ = lean_ctor_get(v_e_1002_, 1);
lean_inc_ref(v_binderType_1056_);
v_body_1057_ = lean_ctor_get(v_e_1002_, 2);
lean_inc_ref(v_body_1057_);
lean_dec_ref_known(v_e_1002_, 3);
v___x_1058_ = 0;
v___x_1059_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1056_, v___x_1058_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
if (v_omitTopForall_1003_ == 0)
{
goto v___jp_1061_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1075_ = lean_string_dec_eq(v_a_1060_, v___x_1074_);
if (v___x_1075_ == 0)
{
goto v___jp_1061_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v_a_1060_);
v___x_1076_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1057_, v_omitTopForall_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1076_;
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1073_; 
v___x_1062_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1057_, v___x_1058_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1068_ = lean_string_append(v___x_1067_, v_a_1060_);
lean_dec(v_a_1060_);
v___x_1069_ = lean_string_append(v___x_1068_, v_a_1063_);
lean_dec(v_a_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
case 3:
{
lean_object* v_u_1077_; 
v_u_1077_ = lean_ctor_get(v_e_1002_, 0);
lean_inc(v_u_1077_);
lean_dec_ref_known(v_e_1002_, 1);
switch(lean_obj_tag(v_u_1077_))
{
case 0:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
case 1:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref_known(v_u_1077_, 1);
v___x_1080_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
default: 
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_u_1077_);
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
}
default: 
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_e_1002_);
v___x_1084_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1086_, uint8_t v_omitTopForall_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; lean_object* v_seen_1095_; uint8_t v___x_1096_; 
v___x_1094_ = lean_st_ref_get(v_a_1088_);
v_seen_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_seen_1095_);
lean_dec(v___x_1094_);
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1095_, v_e_1086_);
lean_dec_ref(v_seen_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1118_; 
lean_inc_ref(v_e_1086_);
v___x_1097_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1086_, v_omitTopForall_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1118_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1118_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v_seen_1103_; lean_object* v_consts_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1117_; 
v___x_1102_ = lean_st_ref_take(v_a_1088_);
v_seen_1103_ = lean_ctor_get(v___x_1102_, 0);
v_consts_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1117_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_consts_1104_);
lean_inc(v_seen_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1117_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1103_, v_e_1086_, v___x_1108_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_consts_1104_);
v___x_1111_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_st_ref_set(v_a_1088_, v___x_1111_);
if (v_isShared_1101_ == 0)
{
v___x_1114_ = v___x_1100_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1098_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v_e_1086_);
v___x_1119_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1121_, lean_object* v_omitTopForall_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_omitTopForall_boxed_1129_; lean_object* v_res_1130_; 
v_omitTopForall_boxed_1129_ = lean_unbox(v_omitTopForall_1122_);
v_res_1130_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1121_, v_omitTopForall_boxed_1129_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1131_, lean_object* v_omitTopForall_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_omitTopForall_boxed_1139_; lean_object* v_res_1140_; 
v_omitTopForall_boxed_1139_ = lean_unbox(v_omitTopForall_1132_);
v_res_1140_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1131_, v_omitTopForall_boxed_1139_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1141_, lean_object* v_m_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1142_, v_a_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
uint8_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1145_, v_m_1146_, v_a_1147_);
lean_dec_ref(v_a_1147_);
lean_dec_ref(v_m_1146_);
v_r_1149_ = lean_box(v_res_1148_);
return v_r_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_1151_, v_a_1152_, v_b_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1155_, lean_object* v_h__1_1156_, lean_object* v_h__2_1157_, lean_object* v_h__3_1158_, lean_object* v_h__4_1159_, lean_object* v_h__5_1160_, lean_object* v_h__6_1161_, lean_object* v_h__7_1162_){
_start:
{
switch(lean_obj_tag(v_e_1155_))
{
case 4:
{
lean_object* v_declName_1163_; lean_object* v_us_1164_; lean_object* v___x_1165_; 
lean_dec(v_h__7_1162_);
lean_dec(v_h__6_1161_);
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
v_declName_1163_ = lean_ctor_get(v_e_1155_, 0);
lean_inc(v_declName_1163_);
v_us_1164_ = lean_ctor_get(v_e_1155_, 1);
lean_inc(v_us_1164_);
lean_dec_ref_known(v_e_1155_, 2);
v___x_1165_ = lean_apply_2(v_h__1_1156_, v_declName_1163_, v_us_1164_);
return v___x_1165_;
}
case 5:
{
lean_object* v_fn_1166_; lean_object* v_arg_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__7_1162_);
lean_dec(v_h__6_1161_);
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__1_1156_);
v_fn_1166_ = lean_ctor_get(v_e_1155_, 0);
lean_inc_ref(v_fn_1166_);
v_arg_1167_ = lean_ctor_get(v_e_1155_, 1);
lean_inc_ref(v_arg_1167_);
lean_dec_ref_known(v_e_1155_, 2);
v___x_1168_ = lean_apply_2(v_h__2_1157_, v_fn_1166_, v_arg_1167_);
return v___x_1168_;
}
case 7:
{
lean_object* v_binderName_1169_; lean_object* v_binderType_1170_; lean_object* v_body_1171_; uint8_t v_binderInfo_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_h__7_1162_);
lean_dec(v_h__6_1161_);
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v_binderName_1169_ = lean_ctor_get(v_e_1155_, 0);
lean_inc(v_binderName_1169_);
v_binderType_1170_ = lean_ctor_get(v_e_1155_, 1);
lean_inc_ref(v_binderType_1170_);
v_body_1171_ = lean_ctor_get(v_e_1155_, 2);
lean_inc_ref(v_body_1171_);
v_binderInfo_1172_ = lean_ctor_get_uint8(v_e_1155_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1155_, 3);
v___x_1173_ = lean_box(v_binderInfo_1172_);
v___x_1174_ = lean_apply_4(v_h__3_1158_, v_binderName_1169_, v_binderType_1170_, v_body_1171_, v___x_1173_);
return v___x_1174_;
}
case 3:
{
lean_object* v_u_1175_; 
lean_dec(v_h__7_1162_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v_u_1175_ = lean_ctor_get(v_e_1155_, 0);
lean_inc(v_u_1175_);
lean_dec_ref_known(v_e_1155_, 1);
switch(lean_obj_tag(v_u_1175_))
{
case 0:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v_h__6_1161_);
lean_dec(v_h__5_1160_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_apply_1(v_h__4_1159_, v___x_1176_);
return v___x_1177_;
}
case 1:
{
lean_object* v_a_1178_; lean_object* v___x_1179_; 
lean_dec(v_h__6_1161_);
lean_dec(v_h__4_1159_);
v_a_1178_ = lean_ctor_get(v_u_1175_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v_u_1175_, 1);
v___x_1179_ = lean_apply_1(v_h__5_1160_, v_a_1178_);
return v___x_1179_;
}
default: 
{
lean_object* v___x_1180_; 
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
v___x_1180_ = lean_apply_3(v_h__6_1161_, v_u_1175_, lean_box(0), lean_box(0));
return v___x_1180_;
}
}
}
default: 
{
lean_object* v___x_1181_; 
lean_dec(v_h__6_1161_);
lean_dec(v_h__5_1160_);
lean_dec(v_h__4_1159_);
lean_dec(v_h__3_1158_);
lean_dec(v_h__2_1157_);
lean_dec(v_h__1_1156_);
v___x_1181_ = lean_apply_7(v_h__7_1162_, v_e_1155_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1182_, lean_object* v_e_1183_, lean_object* v_h__1_1184_, lean_object* v_h__2_1185_, lean_object* v_h__3_1186_, lean_object* v_h__4_1187_, lean_object* v_h__5_1188_, lean_object* v_h__6_1189_, lean_object* v_h__7_1190_){
_start:
{
switch(lean_obj_tag(v_e_1183_))
{
case 4:
{
lean_object* v_declName_1191_; lean_object* v_us_1192_; lean_object* v___x_1193_; 
lean_dec(v_h__7_1190_);
lean_dec(v_h__6_1189_);
lean_dec(v_h__5_1188_);
lean_dec(v_h__4_1187_);
lean_dec(v_h__3_1186_);
lean_dec(v_h__2_1185_);
v_declName_1191_ = lean_ctor_get(v_e_1183_, 0);
lean_inc(v_declName_1191_);
v_us_1192_ = lean_ctor_get(v_e_1183_, 1);
lean_inc(v_us_1192_);
lean_dec_ref_known(v_e_1183_, 2);
v___x_1193_ = lean_apply_2(v_h__1_1184_, v_declName_1191_, v_us_1192_);
return v___x_1193_;
}
case 5:
{
lean_object* v_fn_1194_; lean_object* v_arg_1195_; lean_object* v___x_1196_; 
lean_dec(v_h__7_1190_);
lean_dec(v_h__6_1189_);
lean_dec(v_h__5_1188_);
lean_dec(v_h__4_1187_);
lean_dec(v_h__3_1186_);
lean_dec(v_h__1_1184_);
v_fn_1194_ = lean_ctor_get(v_e_1183_, 0);
lean_inc_ref(v_fn_1194_);
v_arg_1195_ = lean_ctor_get(v_e_1183_, 1);
lean_inc_ref(v_arg_1195_);
lean_dec_ref_known(v_e_1183_, 2);
v___x_1196_ = lean_apply_2(v_h__2_1185_, v_fn_1194_, v_arg_1195_);
return v___x_1196_;
}
case 7:
{
lean_object* v_binderName_1197_; lean_object* v_binderType_1198_; lean_object* v_body_1199_; uint8_t v_binderInfo_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v_h__7_1190_);
lean_dec(v_h__6_1189_);
lean_dec(v_h__5_1188_);
lean_dec(v_h__4_1187_);
lean_dec(v_h__2_1185_);
lean_dec(v_h__1_1184_);
v_binderName_1197_ = lean_ctor_get(v_e_1183_, 0);
lean_inc(v_binderName_1197_);
v_binderType_1198_ = lean_ctor_get(v_e_1183_, 1);
lean_inc_ref(v_binderType_1198_);
v_body_1199_ = lean_ctor_get(v_e_1183_, 2);
lean_inc_ref(v_body_1199_);
v_binderInfo_1200_ = lean_ctor_get_uint8(v_e_1183_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1183_, 3);
v___x_1201_ = lean_box(v_binderInfo_1200_);
v___x_1202_ = lean_apply_4(v_h__3_1186_, v_binderName_1197_, v_binderType_1198_, v_body_1199_, v___x_1201_);
return v___x_1202_;
}
case 3:
{
lean_object* v_u_1203_; 
lean_dec(v_h__7_1190_);
lean_dec(v_h__3_1186_);
lean_dec(v_h__2_1185_);
lean_dec(v_h__1_1184_);
v_u_1203_ = lean_ctor_get(v_e_1183_, 0);
lean_inc(v_u_1203_);
lean_dec_ref_known(v_e_1183_, 1);
switch(lean_obj_tag(v_u_1203_))
{
case 0:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_h__6_1189_);
lean_dec(v_h__5_1188_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_apply_1(v_h__4_1187_, v___x_1204_);
return v___x_1205_;
}
case 1:
{
lean_object* v_a_1206_; lean_object* v___x_1207_; 
lean_dec(v_h__6_1189_);
lean_dec(v_h__4_1187_);
v_a_1206_ = lean_ctor_get(v_u_1203_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v_u_1203_, 1);
v___x_1207_ = lean_apply_1(v_h__5_1188_, v_a_1206_);
return v___x_1207_;
}
default: 
{
lean_object* v___x_1208_; 
lean_dec(v_h__5_1188_);
lean_dec(v_h__4_1187_);
v___x_1208_ = lean_apply_3(v_h__6_1189_, v_u_1203_, lean_box(0), lean_box(0));
return v___x_1208_;
}
}
}
default: 
{
lean_object* v___x_1209_; 
lean_dec(v_h__6_1189_);
lean_dec(v_h__5_1188_);
lean_dec(v_h__4_1187_);
lean_dec(v_h__3_1186_);
lean_dec(v_h__2_1185_);
lean_dec(v_h__1_1184_);
v___x_1209_ = lean_apply_7(v_h__7_1190_, v_e_1183_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1210_, lean_object* v_h__1_1211_, lean_object* v_h__2_1212_){
_start:
{
if (lean_obj_tag(v_x_1210_) == 1)
{
lean_object* v_pre_1213_; lean_object* v_str_1214_; lean_object* v___x_1215_; 
lean_dec(v_h__2_1212_);
v_pre_1213_ = lean_ctor_get(v_x_1210_, 0);
lean_inc(v_pre_1213_);
v_str_1214_ = lean_ctor_get(v_x_1210_, 1);
lean_inc_ref(v_str_1214_);
lean_dec_ref_known(v_x_1210_, 2);
v___x_1215_ = lean_apply_2(v_h__1_1211_, v_pre_1213_, v_str_1214_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_h__1_1211_);
v___x_1216_ = lean_apply_2(v_h__2_1212_, v_x_1210_, lean_box(0));
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1217_, lean_object* v_x_1218_, lean_object* v_h__1_1219_, lean_object* v_h__2_1220_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 1)
{
lean_object* v_pre_1221_; lean_object* v_str_1222_; lean_object* v___x_1223_; 
lean_dec(v_h__2_1220_);
v_pre_1221_ = lean_ctor_get(v_x_1218_, 0);
lean_inc(v_pre_1221_);
v_str_1222_ = lean_ctor_get(v_x_1218_, 1);
lean_inc_ref(v_str_1222_);
lean_dec_ref_known(v_x_1218_, 2);
v___x_1223_ = lean_apply_2(v_h__1_1219_, v_pre_1221_, v_str_1222_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_h__1_1219_);
v___x_1224_ = lean_apply_2(v_h__2_1220_, v_x_1218_, lean_box(0));
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1225_, uint8_t v_omitTopForall_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1225_, v_omitTopForall_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1234_, lean_object* v_omitTopForall_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_omitTopForall_boxed_1242_; lean_object* v_res_1243_; 
v_omitTopForall_boxed_1242_ = lean_unbox(v_omitTopForall_1235_);
v_res_1243_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1234_, v_omitTopForall_boxed_1242_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
if (lean_obj_tag(v_e_1245_) == 7)
{
lean_object* v_binderType_1252_; lean_object* v_body_1253_; lean_object* v___x_1254_; 
v_binderType_1252_ = lean_ctor_get(v_e_1245_, 1);
lean_inc_ref(v_binderType_1252_);
v_body_1253_ = lean_ctor_get(v_e_1245_, 2);
lean_inc_ref(v_body_1253_);
lean_dec_ref_known(v_e_1245_, 3);
v___x_1254_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1253_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_fst_1256_ = lean_ctor_get(v_a_1255_, 0);
v_snd_1257_ = lean_ctor_get(v_a_1255_, 1);
v___x_1258_ = 1;
v___x_1259_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1252_, v___x_1258_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1284_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1265_ = lean_string_dec_eq(v_a_1260_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1278_; 
lean_inc(v_snd_1257_);
lean_inc(v_fst_1256_);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; lean_object* v_unused_1280_; 
v_unused_1279_ = lean_ctor_get(v_a_1255_, 1);
lean_dec(v_unused_1279_);
v_unused_1280_ = lean_ctor_get(v_a_1255_, 0);
lean_dec(v_unused_1280_);
v___x_1267_ = v_a_1255_;
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
else
{
lean_dec(v_a_1255_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1270_ = lean_string_append(v___x_1269_, v_a_1260_);
lean_dec(v_a_1260_);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_fst_1256_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1271_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1257_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1273_);
v___x_1275_ = v___x_1262_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v___x_1282_; 
lean_dec(v_a_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_a_1255_);
v___x_1282_ = v___x_1262_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1255_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_a_1255_);
v_a_1285_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1259_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1259_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_1252_);
return v___x_1254_;
}
}
else
{
uint8_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = 0;
v___x_1294_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1245_, v___x_1293_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1304_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1304_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_a_1295_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1294_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1294_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
return v_x_1321_;
}
else
{
lean_object* v_head_1323_; lean_object* v_tail_1324_; lean_object* v___x_1325_; 
v_head_1323_ = lean_ctor_get(v_x_1322_, 0);
v_tail_1324_ = lean_ctor_get(v_x_1322_, 1);
v___x_1325_ = lean_string_append(v_x_1321_, v_head_1323_);
v_x_1321_ = v___x_1325_;
v_x_1322_ = v_tail_1324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1327_, v_x_1328_);
lean_dec(v_x_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1350_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1350_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1350_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v_fst_1342_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_fst_1342_);
v_snd_1343_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_snd_1343_);
lean_dec(v_a_1338_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1345_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1344_, v_fst_1342_);
lean_dec(v_fst_1342_);
v___x_1346_ = lean_string_append(v_snd_1343_, v___x_1345_);
lean_dec_ref(v___x_1345_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1346_);
v___x_1348_ = v___x_1340_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1337_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1337_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
switch(lean_obj_tag(v_ns_1367_))
{
case 0:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
case 1:
{
lean_object* v_pre_1373_; lean_object* v___x_1374_; lean_object* v_env_1375_; uint8_t v___x_1376_; uint8_t v___x_1377_; 
v_pre_1373_ = lean_ctor_get(v_ns_1367_, 0);
lean_inc(v_pre_1373_);
v___x_1374_ = lean_st_ref_get(v_a_1369_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = 1;
lean_inc_ref(v_ns_1367_);
v___x_1377_ = l_Lean_Environment_contains(v_env_1375_, v_ns_1367_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref_known(v_ns_1367_, 2);
v_ns_1367_ = v_pre_1373_;
goto _start;
}
else
{
lean_object* v___x_1379_; lean_object* v_seen_1380_; lean_object* v_consts_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1395_; 
v___x_1379_ = lean_st_ref_take(v_a_1368_);
v_seen_1380_ = lean_ctor_get(v___x_1379_, 0);
v_consts_1381_ = lean_ctor_get(v___x_1379_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1383_ = v___x_1379_;
v_isShared_1384_ = v_isSharedCheck_1395_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_consts_1381_);
lean_inc(v_seen_1380_);
lean_dec(v___x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1395_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1385_ = lean_box(0);
lean_inc_ref(v_ns_1367_);
v___x_1386_ = l_Lean_Expr_const___override(v_ns_1367_, v___x_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1380_, v___x_1386_, v___x_1387_);
v___x_1389_ = l_Lean_NameSet_insert(v_consts_1381_, v_ns_1367_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1389_);
lean_ctor_set(v___x_1383_, 0, v___x_1388_);
v___x_1391_ = v___x_1383_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_st_ref_set(v_a_1368_, v___x_1391_);
v_ns_1367_ = v_pre_1373_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1396_; 
v_pre_1396_ = lean_ctor_get(v_ns_1367_, 0);
lean_inc(v_pre_1396_);
lean_dec_ref_known(v_ns_1367_, 2);
v_ns_1367_ = v_pre_1396_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec(v_a_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1403_, v_a_1404_, v_a_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = l_Lean_Expr_hasMVar(v_e_1419_);
v___x_1423_ = lean_bool_not(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v_mctx_1425_; lean_object* v___x_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1429_; lean_object* v_cache_1430_; lean_object* v_zetaDeltaFVarIds_1431_; lean_object* v_postponed_1432_; lean_object* v_diag_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v___x_1424_ = lean_st_ref_get(v___y_1420_);
v_mctx_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc_ref(v_mctx_1425_);
lean_dec(v___x_1424_);
v___x_1426_ = l_Lean_instantiateMVarsCore(v_mctx_1425_, v_e_1419_);
v_fst_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_fst_1427_);
v_snd_1428_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_snd_1428_);
lean_dec_ref(v___x_1426_);
v___x_1429_ = lean_st_ref_take(v___y_1420_);
v_cache_1430_ = lean_ctor_get(v___x_1429_, 1);
v_zetaDeltaFVarIds_1431_ = lean_ctor_get(v___x_1429_, 2);
v_postponed_1432_ = lean_ctor_get(v___x_1429_, 3);
v_diag_1433_ = lean_ctor_get(v___x_1429_, 4);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v___x_1429_, 0);
lean_dec(v_unused_1443_);
v___x_1435_ = v___x_1429_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_diag_1433_);
lean_inc(v_postponed_1432_);
lean_inc(v_zetaDeltaFVarIds_1431_);
lean_inc(v_cache_1430_);
lean_dec(v___x_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_snd_1428_);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_snd_1428_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_cache_1430_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_zetaDeltaFVarIds_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_postponed_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_diag_1433_);
v___x_1438_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_st_ref_set(v___y_1420_, v___x_1438_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_fst_1427_);
return v___x_1440_;
}
}
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_e_1419_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1445_, v___y_1446_);
lean_dec(v___y_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1449_, v___y_1452_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v_a_1473_; lean_object* v_currNamespace_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1472_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1465_, v_a_1468_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v_currNamespace_1474_ = lean_ctor_get(v_a_1469_, 6);
lean_inc(v_currNamespace_1474_);
v___x_1475_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1474_, v_a_1466_, v_a_1470_);
lean_dec_ref(v___x_1475_);
v___x_1476_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1473_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1477_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
return v___x_1478_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_a_1479_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1476_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1476_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1496_){
_start:
{
switch(lean_obj_tag(v_x_1496_))
{
case 0:
{
lean_object* v___x_1497_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
return v___x_1497_;
}
case 1:
{
lean_object* v_pre_1498_; lean_object* v_str_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint32_t v___x_1504_; uint32_t v___x_1505_; uint8_t v___x_1506_; 
v_pre_1498_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_pre_1498_);
v_str_1499_ = lean_ctor_get(v_x_1496_, 1);
lean_inc_ref(v_str_1499_);
lean_dec_ref_known(v_x_1496_, 2);
v___x_1500_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1498_);
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_string_utf8_get(v_str_1499_, v___x_1503_);
v___x_1505_ = 65;
v___x_1506_ = lean_uint32_dec_le(v___x_1505_, v___x_1504_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_string_utf8_set(v_str_1499_, v___x_1503_, v___x_1504_);
v___x_1508_ = lean_string_append(v___x_1502_, v___x_1507_);
lean_dec_ref(v___x_1507_);
return v___x_1508_;
}
else
{
uint32_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = 90;
v___x_1510_ = lean_uint32_dec_le(v___x_1504_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_string_utf8_set(v_str_1499_, v___x_1503_, v___x_1504_);
v___x_1512_ = lean_string_append(v___x_1502_, v___x_1511_);
lean_dec_ref(v___x_1511_);
return v___x_1512_;
}
else
{
uint32_t v___x_1513_; uint32_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = 32;
v___x_1514_ = lean_uint32_add(v___x_1504_, v___x_1513_);
v___x_1515_ = lean_string_utf8_set(v_str_1499_, v___x_1503_, v___x_1514_);
v___x_1516_ = lean_string_append(v___x_1502_, v___x_1515_);
lean_dec_ref(v___x_1515_);
return v___x_1516_;
}
}
}
default: 
{
lean_object* v_pre_1517_; 
v_pre_1517_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_pre_1517_);
lean_dec_ref_known(v_x_1496_, 2);
v_x_1496_ = v_pre_1517_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v_env_1522_; lean_object* v___x_1523_; lean_object* v_mainModule_1524_; lean_object* v___x_1525_; 
v___x_1521_ = lean_st_ref_get(v___y_1519_);
v_env_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc_ref(v_env_1522_);
lean_dec(v___x_1521_);
v___x_1523_ = l_Lean_Environment_header(v_env_1522_);
lean_dec_ref(v_env_1522_);
v_mainModule_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_mainModule_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_mainModule_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1526_);
lean_dec(v___y_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1541_) == 0)
{
if (lean_obj_tag(v_x_1542_) == 0)
{
uint8_t v___x_1543_; 
v___x_1543_ = 1;
return v___x_1543_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = 0;
return v___x_1544_;
}
}
else
{
if (lean_obj_tag(v_x_1542_) == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = 0;
return v___x_1545_;
}
else
{
lean_object* v_val_1546_; lean_object* v_val_1547_; uint8_t v___x_1548_; 
v_val_1546_ = lean_ctor_get(v_x_1541_, 0);
v_val_1547_ = lean_ctor_get(v_x_1542_, 0);
v___x_1548_ = lean_name_eq(v_val_1546_, v_val_1547_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1549_, lean_object* v_x_1550_){
_start:
{
uint8_t v_res_1551_; lean_object* v_r_1552_; 
v_res_1551_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1549_, v_x_1550_);
lean_dec(v_x_1550_);
lean_dec(v_x_1549_);
v_r_1552_ = lean_box(v_res_1551_);
return v_r_1552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1553_){
_start:
{
if (lean_obj_tag(v_e_1553_) == 4)
{
lean_object* v_declName_1554_; uint8_t v___x_1555_; 
v_declName_1554_ = lean_ctor_get(v_e_1553_, 0);
v___x_1555_ = l_Lean_Name_hasMacroScopes(v_declName_1554_);
return v___x_1555_;
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = 0;
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1557_);
lean_dec_ref(v_e_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1560_, size_t v_i_1561_, size_t v_stop_1562_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_usize_dec_eq(v_i_1561_, v_stop_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = 1;
v___x_1565_ = lean_array_uget_borrowed(v_as_1560_, v_i_1561_);
if (lean_obj_tag(v___x_1565_) == 0)
{
return v___x_1564_;
}
else
{
if (v___x_1563_ == 0)
{
size_t v___x_1566_; size_t v___x_1567_; 
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1561_, v___x_1566_);
v_i_1561_ = v___x_1567_;
goto _start;
}
else
{
return v___x_1564_;
}
}
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = 0;
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1570_, lean_object* v_i_1571_, lean_object* v_stop_1572_){
_start:
{
size_t v_i_boxed_1573_; size_t v_stop_boxed_1574_; uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_i_boxed_1573_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_stop_boxed_1574_ = lean_unbox_usize(v_stop_1572_);
lean_dec(v_stop_1572_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1570_, v_i_boxed_1573_, v_stop_boxed_1574_);
lean_dec_ref(v_as_1570_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1577_, lean_object* v_as_1578_, size_t v_i_1579_, size_t v_stop_1580_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_usize_dec_eq(v_i_1579_, v_stop_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; lean_object* v___y_1584_; lean_object* v___x_1590_; 
v___x_1582_ = 1;
v___x_1590_ = lean_array_uget(v_as_1578_, v_i_1579_);
if (lean_obj_tag(v___x_1590_) == 0)
{
v___y_1584_ = v___x_1590_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_val_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = l_Lean_Name_getRoot(v_val_1591_);
lean_dec(v_val_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
v___y_1584_ = v___x_1597_;
goto v___jp_1583_;
}
}
}
v___jp_1583_:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
lean_inc(v___x_1577_);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1577_);
v___x_1586_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1584_, v___x_1585_);
lean_dec_ref_known(v___x_1585_, 1);
lean_dec(v___y_1584_);
if (v___x_1586_ == 0)
{
size_t v___x_1587_; size_t v___x_1588_; 
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_add(v_i_1579_, v___x_1587_);
v_i_1579_ = v___x_1588_;
goto _start;
}
else
{
lean_dec(v___x_1577_);
return v___x_1582_;
}
}
}
else
{
uint8_t v___x_1600_; 
lean_dec(v___x_1577_);
v___x_1600_ = 0;
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1601_, lean_object* v_as_1602_, lean_object* v_i_1603_, lean_object* v_stop_1604_){
_start:
{
size_t v_i_boxed_1605_; size_t v_stop_boxed_1606_; uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_i_boxed_1605_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_stop_boxed_1606_ = lean_unbox_usize(v_stop_1604_);
lean_dec(v_stop_1604_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1601_, v_as_1602_, v_i_boxed_1605_, v_stop_boxed_1606_);
lean_dec_ref(v_as_1602_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
lean_ctor_set(v___x_1614_, 2, v___x_1613_);
lean_ctor_set(v___x_1614_, 3, v___x_1613_);
lean_ctor_set(v___x_1614_, 4, v___x_1612_);
lean_ctor_set(v___x_1614_, 5, v___x_1612_);
lean_ctor_set(v___x_1614_, 6, v___x_1612_);
lean_ctor_set(v___x_1614_, 7, v___x_1612_);
lean_ctor_set(v___x_1614_, 8, v___x_1612_);
lean_ctor_set(v___x_1614_, 9, v___x_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_unsigned_to_nat(32u);
v___x_1616_ = lean_mk_empty_array_with_capacity(v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = ((size_t)5ULL);
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_unsigned_to_nat(32u);
v___x_1621_ = lean_mk_empty_array_with_capacity(v___x_1620_);
v___x_1622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1623_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___x_1621_);
lean_ctor_set(v___x_1623_, 2, v___x_1619_);
lean_ctor_set(v___x_1623_, 3, v___x_1619_);
lean_ctor_set_usize(v___x_1623_, 4, v___x_1618_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = lean_box(1);
v___x_1625_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
lean_ctor_set(v___x_1627_, 2, v___x_1624_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1630_ = l_Lean_stringToMessageData(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1633_ = l_Lean_stringToMessageData(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1649_, lean_object* v_declHint_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_env_1654_; uint8_t v___y_1656_; uint8_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1653_ = lean_st_ref_get(v___y_1651_);
v_env_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref(v_env_1654_);
lean_dec(v___x_1653_);
v___x_1712_ = l_Lean_Name_isAnonymous(v_declHint_1650_);
v___x_1713_ = lean_bool_not(v___x_1712_);
if (v___x_1713_ == 0)
{
v___y_1656_ = v___x_1713_;
goto v___jp_1655_;
}
else
{
uint8_t v_isExporting_1714_; 
v_isExporting_1714_ = lean_ctor_get_uint8(v_env_1654_, sizeof(void*)*8);
v___y_1656_ = v_isExporting_1714_;
goto v___jp_1655_;
}
v___jp_1655_:
{
if (v___y_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v_env_1654_);
lean_dec(v_declHint_1650_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_msg_1649_);
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1658_ = 0;
lean_inc_ref(v_env_1654_);
v___x_1659_ = l_Lean_Environment_setExporting(v_env_1654_, v___x_1658_);
lean_inc(v_declHint_1650_);
lean_inc_ref(v___x_1659_);
v___x_1660_ = l_Lean_Environment_contains(v___x_1659_, v_declHint_1650_, v___y_1656_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_env_1654_);
lean_dec(v_declHint_1650_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_msg_1649_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_c_1667_; lean_object* v___x_1668_; 
v___x_1662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1664_ = l_Lean_Options_empty;
v___x_1665_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1659_);
lean_ctor_set(v___x_1665_, 1, v___x_1662_);
lean_ctor_set(v___x_1665_, 2, v___x_1663_);
lean_ctor_set(v___x_1665_, 3, v___x_1664_);
lean_inc(v_declHint_1650_);
v___x_1666_ = l_Lean_MessageData_ofConstName(v_declHint_1650_, v___x_1658_);
v_c_1667_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1667_, 0, v___x_1665_);
lean_ctor_set(v_c_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1654_, v_declHint_1650_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref(v_env_1654_);
lean_dec(v_declHint_1650_);
v___x_1669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_c_1667_);
v___x_1671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_MessageData_note(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_msg_1649_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1711_; 
v_val_1676_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1678_ = v___x_1668_;
v_isShared_1679_ = v_isSharedCheck_1711_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_val_1676_);
lean_dec(v___x_1668_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1711_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_mod_1683_; uint8_t v___x_1684_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Lean_Environment_header(v_env_1654_);
lean_dec_ref(v_env_1654_);
v___x_1682_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1681_);
v_mod_1683_ = lean_array_get(v___x_1680_, v___x_1682_, v_val_1676_);
lean_dec(v_val_1676_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = l_Lean_isPrivateName(v_declHint_1650_);
lean_dec(v_declHint_1650_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v_c_1667_);
v___x_1687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_MessageData_ofName(v_mod_1683_);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_MessageData_note(v___x_1692_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_msg_1649_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1694_);
v___x_1696_ = v___x_1678_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v_c_1667_);
v___x_1700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_MessageData_ofName(v_mod_1683_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_MessageData_note(v___x_1705_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_msg_1649_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1707_);
v___x_1709_ = v___x_1678_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1715_, lean_object* v_declHint_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1715_, v_declHint_1716_, v___y_1717_);
lean_dec(v___y_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1720_, lean_object* v_declHint_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v___x_1727_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1720_, v_declHint_1721_, v___y_1725_);
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = l_Lean_unknownIdentifierMessageTag;
v___x_1733_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1728_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1738_, lean_object* v_declHint_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1738_, v_declHint_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1746_, lean_object* v_msg_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_fileName_1753_; lean_object* v_fileMap_1754_; lean_object* v_options_1755_; lean_object* v_currRecDepth_1756_; lean_object* v_maxRecDepth_1757_; lean_object* v_ref_1758_; lean_object* v_currNamespace_1759_; lean_object* v_openDecls_1760_; lean_object* v_initHeartbeats_1761_; lean_object* v_maxHeartbeats_1762_; lean_object* v_quotContext_1763_; lean_object* v_currMacroScope_1764_; uint8_t v_diag_1765_; lean_object* v_cancelTk_x3f_1766_; uint8_t v_suppressElabErrors_1767_; lean_object* v_inheritedTraceOptions_1768_; lean_object* v_ref_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_fileName_1753_ = lean_ctor_get(v___y_1750_, 0);
v_fileMap_1754_ = lean_ctor_get(v___y_1750_, 1);
v_options_1755_ = lean_ctor_get(v___y_1750_, 2);
v_currRecDepth_1756_ = lean_ctor_get(v___y_1750_, 3);
v_maxRecDepth_1757_ = lean_ctor_get(v___y_1750_, 4);
v_ref_1758_ = lean_ctor_get(v___y_1750_, 5);
v_currNamespace_1759_ = lean_ctor_get(v___y_1750_, 6);
v_openDecls_1760_ = lean_ctor_get(v___y_1750_, 7);
v_initHeartbeats_1761_ = lean_ctor_get(v___y_1750_, 8);
v_maxHeartbeats_1762_ = lean_ctor_get(v___y_1750_, 9);
v_quotContext_1763_ = lean_ctor_get(v___y_1750_, 10);
v_currMacroScope_1764_ = lean_ctor_get(v___y_1750_, 11);
v_diag_1765_ = lean_ctor_get_uint8(v___y_1750_, sizeof(void*)*14);
v_cancelTk_x3f_1766_ = lean_ctor_get(v___y_1750_, 12);
v_suppressElabErrors_1767_ = lean_ctor_get_uint8(v___y_1750_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1768_ = lean_ctor_get(v___y_1750_, 13);
v_ref_1769_ = l_Lean_replaceRef(v_ref_1746_, v_ref_1758_);
lean_inc_ref(v_inheritedTraceOptions_1768_);
lean_inc(v_cancelTk_x3f_1766_);
lean_inc(v_currMacroScope_1764_);
lean_inc(v_quotContext_1763_);
lean_inc(v_maxHeartbeats_1762_);
lean_inc(v_initHeartbeats_1761_);
lean_inc(v_openDecls_1760_);
lean_inc(v_currNamespace_1759_);
lean_inc(v_maxRecDepth_1757_);
lean_inc(v_currRecDepth_1756_);
lean_inc_ref(v_options_1755_);
lean_inc_ref(v_fileMap_1754_);
lean_inc_ref(v_fileName_1753_);
v___x_1770_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1770_, 0, v_fileName_1753_);
lean_ctor_set(v___x_1770_, 1, v_fileMap_1754_);
lean_ctor_set(v___x_1770_, 2, v_options_1755_);
lean_ctor_set(v___x_1770_, 3, v_currRecDepth_1756_);
lean_ctor_set(v___x_1770_, 4, v_maxRecDepth_1757_);
lean_ctor_set(v___x_1770_, 5, v_ref_1769_);
lean_ctor_set(v___x_1770_, 6, v_currNamespace_1759_);
lean_ctor_set(v___x_1770_, 7, v_openDecls_1760_);
lean_ctor_set(v___x_1770_, 8, v_initHeartbeats_1761_);
lean_ctor_set(v___x_1770_, 9, v_maxHeartbeats_1762_);
lean_ctor_set(v___x_1770_, 10, v_quotContext_1763_);
lean_ctor_set(v___x_1770_, 11, v_currMacroScope_1764_);
lean_ctor_set(v___x_1770_, 12, v_cancelTk_x3f_1766_);
lean_ctor_set(v___x_1770_, 13, v_inheritedTraceOptions_1768_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*14, v_diag_1765_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*14 + 1, v_suppressElabErrors_1767_);
v___x_1771_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1747_, v___y_1748_, v___y_1749_, v___x_1770_, v___y_1751_);
lean_dec_ref_known(v___x_1770_, 14);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1772_, v_msg_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v_ref_1772_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1780_, lean_object* v_msg_1781_, lean_object* v_declHint_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1790_; 
v___x_1788_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1781_, v_declHint_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1780_, v_a_1789_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v_declHint_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1791_, v_msg_1792_, v_declHint_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v_ref_1791_);
return v_res_1799_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1806_, lean_object* v_constName_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1813_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1814_ = 0;
lean_inc(v_constName_1807_);
v___x_1815_ = l_Lean_MessageData_ofConstName(v_constName_1807_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1806_, v___x_1818_, v_constName_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1820_, lean_object* v_constName_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1820_, v_constName_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v_ref_1820_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_ref_1834_; lean_object* v___x_1835_; 
v_ref_1834_ = lean_ctor_get(v___y_1831_, 5);
v___x_1835_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1834_, v_constName_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_env_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_st_ref_get(v___y_1847_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = 0;
lean_inc(v_constName_1843_);
v___x_1852_ = l_Lean_Environment_find_x3f(v_env_1850_, v_constName_1843_, v___x_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1853_;
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_constName_1843_);
v_val_1854_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1852_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v___x_1852_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 0);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_val_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
lean_inc(v_declName_1869_);
v___x_1875_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1875_, 0);
lean_dec(v_unused_1903_);
v___x_1877_ = v___x_1875_;
v_isShared_1878_ = v_isSharedCheck_1902_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v___x_1875_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1902_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v_env_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_st_ref_get(v___y_1873_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_ref(v_env_1880_);
lean_dec(v___x_1879_);
v___x_1881_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1880_, v_declName_1869_);
lean_dec(v_declName_1869_);
lean_dec_ref(v_env_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_box(0);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1882_);
v___x_1884_ = v___x_1877_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1901_; 
v_val_1886_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1888_ = v___x_1881_;
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v___x_1881_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1901_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1890_ = lean_st_ref_get(v___y_1873_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Lean_Environment_allImportedModuleNames(v_env_1891_);
lean_dec_ref(v_env_1891_);
v___x_1894_ = lean_array_get(v___x_1892_, v___x_1893_, v_val_1886_);
lean_dec(v_val_1886_);
lean_dec_ref(v___x_1893_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1894_);
v___x_1896_ = v___x_1888_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1896_);
v___x_1898_ = v___x_1877_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_declName_1869_);
v_a_1904_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1875_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1875_);
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
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_object* v_k_1926_; lean_object* v_l_1927_; lean_object* v_r_1928_; lean_object* v___x_1929_; 
v_k_1926_ = lean_ctor_get(v_x_1920_, 1);
lean_inc(v_k_1926_);
v_l_1927_ = lean_ctor_get(v_x_1920_, 3);
lean_inc(v_l_1927_);
v_r_1928_ = lean_ctor_get(v_x_1920_, 4);
lean_inc(v_r_1928_);
lean_dec_ref_known(v_x_1920_, 5);
v___x_1929_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1919_, v_l_1927_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_1926_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = lean_array_push(v_a_1930_, v_a_1932_);
v_init_1919_ = v___x_1933_;
v_x_1920_ = v_r_1928_;
goto _start;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1930_);
lean_dec(v_r_1928_);
v_a_1935_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1931_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1931_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_dec(v_r_1928_);
lean_dec(v_k_1926_);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_init_1919_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_1944_, lean_object* v_x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1944_, v_x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1951_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_NameSet_empty;
v___x_1953_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_1956_, lean_object* v_type_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0);
v___x_1965_ = lean_st_mk_ref(v___x_1964_);
lean_inc_ref(v_type_1957_);
v___x_1966_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_1957_, v___x_1965_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2019_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = lean_st_ref_get(v___x_1965_);
lean_dec(v___x_1965_);
v___x_1969_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_1961_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2019_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2019_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_consts_1974_; lean_object* v___f_1975_; lean_object* v___y_1977_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___y_1988_; lean_object* v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_2001_; 
v_consts_1974_ = lean_ctor_get(v___x_1968_, 1);
lean_inc(v_consts_1974_);
lean_dec(v___x_1968_);
v___f_1975_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1));
v___x_1985_ = lean_string_append(v_pre_1956_, v_a_1967_);
lean_dec(v_a_1967_);
v___x_1986_ = l_Lean_Name_getRoot(v_a_1970_);
lean_dec(v_a_1970_);
if (lean_obj_tag(v_consts_1974_) == 0)
{
lean_object* v_size_2018_; 
v_size_2018_ = lean_ctor_get(v_consts_1974_, 0);
lean_inc(v_size_2018_);
v___y_2001_ = v_size_2018_;
goto v___jp_2000_;
}
else
{
v___y_2001_ = v___x_1963_;
goto v___jp_2000_;
}
v___jp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = l_Lean_Name_str___override(v___x_1978_, v___y_1977_);
v___x_1980_ = lean_find_expr(v___f_1975_, v_type_1957_);
lean_dec_ref(v_type_1957_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1979_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1979_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_object* v___x_1984_; 
lean_dec_ref_known(v___x_1980_, 1);
lean_del_object(v___x_1972_);
v___x_1984_ = l_Lean_Core_mkFreshUserName(v___x_1979_, v_a_1960_, v_a_1961_);
return v___x_1984_;
}
}
v___jp_1987_:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_bool_not(v___y_1988_);
if (v___x_1989_ == 0)
{
lean_dec(v___x_1986_);
v___y_1977_ = v___x_1985_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_1986_);
v___x_1991_ = lean_string_append(v___x_1985_, v___x_1990_);
lean_dec_ref(v___x_1990_);
v___y_1977_ = v___x_1991_;
goto v___jp_1976_;
}
}
v___jp_1992_:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_lt(v___x_1963_, v___y_1994_);
if (v___x_1996_ == 0)
{
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
v___y_1988_ = v___y_1995_;
goto v___jp_1987_;
}
else
{
if (v___x_1996_ == 0)
{
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
v___y_1988_ = v___y_1995_;
goto v___jp_1987_;
}
else
{
size_t v___x_1997_; size_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = lean_usize_of_nat(v___y_1994_);
lean_dec(v___y_1994_);
lean_inc(v___x_1986_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1986_, v___y_1993_, v___x_1997_, v___x_1998_);
lean_dec_ref(v___y_1993_);
v___y_1988_ = v___x_1999_;
goto v___jp_1987_;
}
}
}
v___jp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_mk_empty_array_with_capacity(v___y_2001_);
lean_dec(v___y_2001_);
v___x_2003_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_2002_, v_consts_1974_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = lean_array_get_size(v_a_2004_);
v___x_2006_ = lean_nat_dec_lt(v___x_1963_, v___x_2005_);
if (v___x_2006_ == 0)
{
v___y_1993_ = v_a_2004_;
v___y_1994_ = v___x_2005_;
v___y_1995_ = v___x_2006_;
goto v___jp_1992_;
}
else
{
if (v___x_2006_ == 0)
{
v___y_1993_ = v_a_2004_;
v___y_1994_ = v___x_2005_;
v___y_1995_ = v___x_2006_;
goto v___jp_1992_;
}
else
{
size_t v___x_2007_; size_t v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = lean_usize_of_nat(v___x_2005_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_2004_, v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
v___y_1993_ = v_a_2004_;
v___y_1994_ = v___x_2005_;
v___y_1995_ = v___x_2009_;
goto v___jp_1992_;
}
else
{
lean_dec(v_a_2004_);
v___y_1988_ = v___x_2009_;
goto v___jp_1987_;
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v___x_1986_);
lean_dec_ref(v___x_1985_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_type_1957_);
v_a_2010_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2003_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2003_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v___x_1965_);
lean_dec_ref(v_type_1957_);
lean_dec_ref(v_pre_1956_);
v_a_2020_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1966_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1966_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_2028_, lean_object* v_type_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2028_, v_type_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2036_, lean_object* v_constName_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_constName_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2044_, v_constName_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2052_, lean_object* v_ref_2053_, lean_object* v_constName_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2053_, v_constName_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_ref_2062_, lean_object* v_constName_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2061_, v_ref_2062_, v_constName_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v_ref_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2070_, lean_object* v_ref_2071_, lean_object* v_msg_2072_, lean_object* v_declHint_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2071_, v_msg_2072_, v_declHint_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_ref_2081_, lean_object* v_msg_2082_, lean_object* v_declHint_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2080_, v_ref_2081_, v_msg_2082_, v_declHint_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v_ref_2081_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2090_, lean_object* v_declHint_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2090_, v_declHint_2091_, v___y_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2098_, lean_object* v_declHint_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2098_, v_declHint_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2106_, lean_object* v_ref_2107_, lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2107_, v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2115_, lean_object* v_ref_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2115_, v_ref_2116_, v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v_ref_2116_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2142_, lean_object* v_a_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_a_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2152_, v_a_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2162_, lean_object* v_binds_2163_, lean_object* v_pre_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Elab_Term_elabType(v_type_2162_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = 0;
v___x_2175_ = 1;
v___x_2176_ = 1;
v___x_2177_ = l_Lean_Meta_mkForallFVars(v_binds_2163_, v_a_2173_, v___x_2174_, v___x_2175_, v___x_2175_, v___x_2176_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2164_, v_a_2178_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2179_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_pre_2164_);
v_a_2180_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2177_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2177_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_pre_2164_);
v_a_2188_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2172_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2172_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2196_, lean_object* v_binds_2197_, lean_object* v_pre_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2196_, v_binds_2197_, v_pre_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_binds_2197_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2207_, lean_object* v_pre_2208_, lean_object* v_binds_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___f_2217_; lean_object* v___x_2218_; 
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2217_, 0, v_type_2207_);
lean_closure_set(v___f_2217_, 1, v_binds_2209_);
lean_closure_set(v___f_2217_, 2, v_pre_2208_);
v___x_2218_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2217_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2219_, lean_object* v_pre_2220_, lean_object* v_binds_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2219_, v_pre_2220_, v_binds_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_currNamespace_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_currNamespace_2230_);
lean_ctor_set(v___x_2233_, 1, v___y_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_currNamespace_2234_, v___y_2235_, v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2238_, lean_object* v_declName_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v___x_2242_; lean_object* v_env_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2242_ = 0;
v_env_2243_ = l_Lean_Environment_setExporting(v_env_2238_, v___x_2242_);
lean_inc(v_declName_2239_);
v___x_2244_ = l_Lean_mkPrivateName(v_env_2243_, v_declName_2239_);
v___x_2245_ = 1;
lean_inc_ref(v_env_2243_);
v___x_2246_ = l_Lean_Environment_contains(v_env_2243_, v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2247_ = l_Lean_privateToUserName(v_declName_2239_);
v___x_2248_ = l_Lean_Environment_contains(v_env_2243_, v___x_2247_, v___x_2245_);
v___x_2249_ = lean_box(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___y_2241_);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declName_2239_);
v___x_2251_ = lean_box(v___x_2246_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___y_2241_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2253_, lean_object* v_declName_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2253_, v_declName_2254_, v___y_2255_, v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2258_, lean_object* v___y_2259_){
_start:
{
if (lean_obj_tag(v_x_2258_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v_x_2258_, 0);
lean_inc(v_a_2260_);
v___x_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2260_);
lean_ctor_set(v___x_2261_, 1, v___y_2259_);
return v___x_2261_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v_x_2258_, 0);
lean_inc(v_a_2262_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2262_);
lean_ctor_set(v___x_2263_, 1, v___y_2259_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2264_, v___y_2265_);
lean_dec_ref(v_x_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2267_, lean_object* v_stx_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2267_, v_stx_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
if (lean_obj_tag(v_a_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
v_a_2273_ = lean_ctor_get(v___x_2271_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v___x_2271_, 0);
lean_dec(v_unused_2282_);
v___x_2275_ = v___x_2271_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_box(0);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_a_2273_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2311_; 
v_val_2283_ = lean_ctor_get(v_a_2272_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_a_2272_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2285_ = v_a_2272_;
v_isShared_2286_ = v_isSharedCheck_2311_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_val_2283_);
lean_dec(v_a_2272_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2311_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_snd_2287_; 
v_snd_2287_ = lean_ctor_get(v_val_2283_, 1);
lean_inc(v_snd_2287_);
lean_dec(v_val_2283_);
if (lean_obj_tag(v_snd_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
lean_del_object(v___x_2285_);
v_a_2288_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2271_, 2);
v_a_2289_ = lean_ctor_get(v_snd_2287_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_snd_2287_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2291_ = v_snd_2287_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v_snd_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
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
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2294_, v_a_2288_);
lean_dec_ref(v___x_2294_);
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_a_2298_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2271_, 2);
v_a_2299_ = lean_ctor_get(v_snd_2287_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_snd_2287_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2301_ = v_snd_2287_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v_snd_2287_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v_a_2299_);
v___x_2304_ = v___x_2285_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2306_, v_a_2298_);
lean_dec_ref(v___x_2306_);
return v___x_2307_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2312_ = lean_ctor_get(v___x_2271_, 0);
v_a_2313_ = lean_ctor_get(v___x_2271_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2271_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_inc(v_a_2312_);
lean_dec(v___x_2271_);
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
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2312_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_a_2313_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2321_, lean_object* v_stx_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2321_, v_stx_2322_, v___y_2323_, v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object* v_opts_2326_, lean_object* v_opt_2327_){
_start:
{
lean_object* v_name_2328_; lean_object* v_defValue_2329_; lean_object* v_map_2330_; lean_object* v___x_2331_; 
v_name_2328_ = lean_ctor_get(v_opt_2327_, 0);
v_defValue_2329_ = lean_ctor_get(v_opt_2327_, 1);
v_map_2330_ = lean_ctor_get(v_opts_2326_, 0);
v___x_2331_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2330_, v_name_2328_);
if (lean_obj_tag(v___x_2331_) == 0)
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_unbox(v_defValue_2329_);
return v___x_2332_;
}
else
{
lean_object* v_val_2333_; 
v_val_2333_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v___x_2331_, 1);
if (lean_obj_tag(v_val_2333_) == 1)
{
uint8_t v_v_2334_; 
v_v_2334_ = lean_ctor_get_uint8(v_val_2333_, 0);
lean_dec_ref_known(v_val_2333_, 0);
return v_v_2334_;
}
else
{
uint8_t v___x_2335_; 
lean_dec(v_val_2333_);
v___x_2335_ = lean_unbox(v_defValue_2329_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_opts_2336_, lean_object* v_opt_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2336_, v_opt_2337_);
lean_dec_ref(v_opt_2337_);
lean_dec_ref(v_opts_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(1);
v___x_2341_ = l_Lean_MessageData_ofFormat(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2));
v___x_2346_ = l_Lean_MessageData_ofFormat(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
if (lean_obj_tag(v_x_2348_) == 0)
{
return v_x_2347_;
}
else
{
lean_object* v_head_2349_; lean_object* v_tail_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2372_; 
v_head_2349_ = lean_ctor_get(v_x_2348_, 0);
v_tail_2350_ = lean_ctor_get(v_x_2348_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2348_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2352_ = v_x_2348_;
v_isShared_2353_ = v_isSharedCheck_2372_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_tail_2350_);
lean_inc(v_head_2349_);
lean_dec(v_x_2348_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2372_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_before_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2370_; 
v_before_2354_ = lean_ctor_get(v_head_2349_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_head_2349_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_head_2349_, 1);
lean_dec(v_unused_2371_);
v___x_2356_ = v_head_2349_;
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_before_2354_);
lean_dec(v_head_2349_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 7);
lean_ctor_set(v___x_2356_, 1, v___x_2358_);
lean_ctor_set(v___x_2356_, 0, v_x_2347_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_x_2347_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 7);
lean_ctor_set(v___x_2352_, 1, v___x_2361_);
lean_ctor_set(v___x_2352_, 0, v___x_2360_);
v___x_2363_ = v___x_2352_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_MessageData_ofSyntax(v_before_2354_);
v___x_2365_ = l_Lean_indentD(v___x_2364_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v_x_2347_ = v___x_2366_;
v_x_2348_ = v_tail_2350_;
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
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2377_ = l_Lean_MessageData_ofFormat(v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2378_, lean_object* v_macroStack_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_options_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; uint8_t v___x_2385_; 
v_options_2382_ = lean_ctor_get(v___y_2380_, 2);
v___x_2383_ = l_Lean_Elab_pp_macroStack;
v___x_2384_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_options_2382_, v___x_2383_);
v___x_2385_ = lean_bool_not(v___x_2384_);
if (v___x_2385_ == 0)
{
if (lean_obj_tag(v_macroStack_2379_) == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_msgData_2378_);
return v___x_2386_;
}
else
{
lean_object* v_head_2387_; lean_object* v_after_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2403_; 
v_head_2387_ = lean_ctor_get(v_macroStack_2379_, 0);
lean_inc(v_head_2387_);
v_after_2388_ = lean_ctor_get(v_head_2387_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_head_2387_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_head_2387_, 0);
lean_dec(v_unused_2404_);
v___x_2390_ = v_head_2387_;
v_isShared_2391_ = v_isSharedCheck_2403_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_after_2388_);
lean_dec(v_head_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2403_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 7);
lean_ctor_set(v___x_2390_, 1, v___x_2392_);
lean_ctor_set(v___x_2390_, 0, v_msgData_2378_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_msgData_2378_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_msgData_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2395_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_MessageData_ofSyntax(v_after_2388_);
v___x_2398_ = l_Lean_indentD(v___x_2397_);
v_msgData_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2399_, 0, v___x_2396_);
lean_ctor_set(v_msgData_2399_, 1, v___x_2398_);
v___x_2400_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_2399_, v_macroStack_2379_);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
}
}
else
{
lean_object* v___x_2405_; 
lean_dec(v_macroStack_2379_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v_msgData_2378_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2406_, lean_object* v_macroStack_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2406_, v_macroStack_2407_, v___y_2408_);
lean_dec_ref(v___y_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_ref_2419_; lean_object* v___x_2420_; lean_object* v_a_2421_; lean_object* v_macroStack_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2433_; 
v_ref_2419_ = lean_ctor_get(v___y_2416_, 5);
v___x_2420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2411_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v_macroStack_2422_ = lean_ctor_get(v___y_2412_, 1);
v___x_2423_ = l_Lean_Elab_getBetterRef(v_ref_2419_, v_macroStack_2422_);
lean_inc(v_macroStack_2422_);
v___x_2424_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2421_, v_macroStack_2422_, v___y_2416_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2423_);
lean_ctor_set(v___x_2429_, 1, v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set_tag(v___x_2427_, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_fileName_2452_; lean_object* v_fileMap_2453_; lean_object* v_options_2454_; lean_object* v_currRecDepth_2455_; lean_object* v_maxRecDepth_2456_; lean_object* v_ref_2457_; lean_object* v_currNamespace_2458_; lean_object* v_openDecls_2459_; lean_object* v_initHeartbeats_2460_; lean_object* v_maxHeartbeats_2461_; lean_object* v_quotContext_2462_; lean_object* v_currMacroScope_2463_; uint8_t v_diag_2464_; lean_object* v_cancelTk_x3f_2465_; uint8_t v_suppressElabErrors_2466_; lean_object* v_inheritedTraceOptions_2467_; lean_object* v_ref_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_fileName_2452_ = lean_ctor_get(v___y_2449_, 0);
v_fileMap_2453_ = lean_ctor_get(v___y_2449_, 1);
v_options_2454_ = lean_ctor_get(v___y_2449_, 2);
v_currRecDepth_2455_ = lean_ctor_get(v___y_2449_, 3);
v_maxRecDepth_2456_ = lean_ctor_get(v___y_2449_, 4);
v_ref_2457_ = lean_ctor_get(v___y_2449_, 5);
v_currNamespace_2458_ = lean_ctor_get(v___y_2449_, 6);
v_openDecls_2459_ = lean_ctor_get(v___y_2449_, 7);
v_initHeartbeats_2460_ = lean_ctor_get(v___y_2449_, 8);
v_maxHeartbeats_2461_ = lean_ctor_get(v___y_2449_, 9);
v_quotContext_2462_ = lean_ctor_get(v___y_2449_, 10);
v_currMacroScope_2463_ = lean_ctor_get(v___y_2449_, 11);
v_diag_2464_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*14);
v_cancelTk_x3f_2465_ = lean_ctor_get(v___y_2449_, 12);
v_suppressElabErrors_2466_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2467_ = lean_ctor_get(v___y_2449_, 13);
v_ref_2468_ = l_Lean_replaceRef(v_ref_2443_, v_ref_2457_);
lean_inc_ref(v_inheritedTraceOptions_2467_);
lean_inc(v_cancelTk_x3f_2465_);
lean_inc(v_currMacroScope_2463_);
lean_inc(v_quotContext_2462_);
lean_inc(v_maxHeartbeats_2461_);
lean_inc(v_initHeartbeats_2460_);
lean_inc(v_openDecls_2459_);
lean_inc(v_currNamespace_2458_);
lean_inc(v_maxRecDepth_2456_);
lean_inc(v_currRecDepth_2455_);
lean_inc_ref(v_options_2454_);
lean_inc_ref(v_fileMap_2453_);
lean_inc_ref(v_fileName_2452_);
v___x_2469_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2469_, 0, v_fileName_2452_);
lean_ctor_set(v___x_2469_, 1, v_fileMap_2453_);
lean_ctor_set(v___x_2469_, 2, v_options_2454_);
lean_ctor_set(v___x_2469_, 3, v_currRecDepth_2455_);
lean_ctor_set(v___x_2469_, 4, v_maxRecDepth_2456_);
lean_ctor_set(v___x_2469_, 5, v_ref_2468_);
lean_ctor_set(v___x_2469_, 6, v_currNamespace_2458_);
lean_ctor_set(v___x_2469_, 7, v_openDecls_2459_);
lean_ctor_set(v___x_2469_, 8, v_initHeartbeats_2460_);
lean_ctor_set(v___x_2469_, 9, v_maxHeartbeats_2461_);
lean_ctor_set(v___x_2469_, 10, v_quotContext_2462_);
lean_ctor_set(v___x_2469_, 11, v_currMacroScope_2463_);
lean_ctor_set(v___x_2469_, 12, v_cancelTk_x3f_2465_);
lean_ctor_set(v___x_2469_, 13, v_inheritedTraceOptions_2467_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*14, v_diag_2464_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*14 + 1, v_suppressElabErrors_2466_);
v___x_2470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___x_2469_, v___y_2450_);
lean_dec_ref_known(v___x_2469_, 14);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2471_, lean_object* v_msg_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2471_, v_msg_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_ref_2471_);
return v_res_2480_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2481_; double v___x_2482_; 
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = lean_float_of_nat(v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_ref_2492_; lean_object* v___x_2493_; lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2538_; 
v_ref_2492_ = lean_ctor_get(v___y_2489_, 5);
v___x_2493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2538_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2538_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v_traceState_2499_; lean_object* v_env_2500_; lean_object* v_nextMacroScope_2501_; lean_object* v_ngen_2502_; lean_object* v_auxDeclNGen_2503_; lean_object* v_cache_2504_; lean_object* v_messages_2505_; lean_object* v_infoState_2506_; lean_object* v_snapshotTasks_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2537_; 
v___x_2498_ = lean_st_ref_take(v___y_2490_);
v_traceState_2499_ = lean_ctor_get(v___x_2498_, 4);
v_env_2500_ = lean_ctor_get(v___x_2498_, 0);
v_nextMacroScope_2501_ = lean_ctor_get(v___x_2498_, 1);
v_ngen_2502_ = lean_ctor_get(v___x_2498_, 2);
v_auxDeclNGen_2503_ = lean_ctor_get(v___x_2498_, 3);
v_cache_2504_ = lean_ctor_get(v___x_2498_, 5);
v_messages_2505_ = lean_ctor_get(v___x_2498_, 6);
v_infoState_2506_ = lean_ctor_get(v___x_2498_, 7);
v_snapshotTasks_2507_ = lean_ctor_get(v___x_2498_, 8);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2537_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_snapshotTasks_2507_);
lean_inc(v_infoState_2506_);
lean_inc(v_messages_2505_);
lean_inc(v_cache_2504_);
lean_inc(v_traceState_2499_);
lean_inc(v_auxDeclNGen_2503_);
lean_inc(v_ngen_2502_);
lean_inc(v_nextMacroScope_2501_);
lean_inc(v_env_2500_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2537_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
uint64_t v_tid_2511_; lean_object* v_traces_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2536_; 
v_tid_2511_ = lean_ctor_get_uint64(v_traceState_2499_, sizeof(void*)*1);
v_traces_2512_ = lean_ctor_get(v_traceState_2499_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_traceState_2499_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2514_ = v_traceState_2499_;
v_isShared_2515_ = v_isSharedCheck_2536_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_traces_2512_);
lean_dec(v_traceState_2499_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2536_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; double v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2518_ = 0;
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2520_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2520_, 0, v_cls_2485_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
lean_ctor_set(v___x_2520_, 2, v___x_2519_);
lean_ctor_set_float(v___x_2520_, sizeof(void*)*3, v___x_2517_);
lean_ctor_set_float(v___x_2520_, sizeof(void*)*3 + 8, v___x_2517_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*3 + 16, v___x_2518_);
v___x_2521_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2522_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v_a_2494_);
lean_ctor_set(v___x_2522_, 2, v___x_2521_);
lean_inc(v_ref_2492_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_ref_2492_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_PersistentArray_push___redArg(v_traces_2512_, v___x_2523_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2524_);
v___x_2526_ = v___x_2514_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2524_);
lean_ctor_set_uint64(v_reuseFailAlloc_2535_, sizeof(void*)*1, v_tid_2511_);
v___x_2526_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 4, v___x_2526_);
v___x_2528_ = v___x_2509_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_env_2500_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_nextMacroScope_2501_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_ngen_2502_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_auxDeclNGen_2503_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2534_, 5, v_cache_2504_);
lean_ctor_set(v_reuseFailAlloc_2534_, 6, v_messages_2505_);
lean_ctor_set(v_reuseFailAlloc_2534_, 7, v_infoState_2506_);
lean_ctor_set(v_reuseFailAlloc_2534_, 8, v_snapshotTasks_2507_);
v___x_2528_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_st_ref_set(v___y_2490_, v___x_2528_);
v___x_2530_ = lean_box(0);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2530_);
v___x_2532_ = v___x_2496_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2539_, lean_object* v_msg_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2539_, v_msg_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
if (lean_obj_tag(v_as_2550_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
else
{
lean_object* v_options_2560_; uint8_t v_hasTrace_2561_; 
v_options_2560_ = lean_ctor_get(v___y_2555_, 2);
v_hasTrace_2561_ = lean_ctor_get_uint8(v_options_2560_, sizeof(void*)*1);
if (v_hasTrace_2561_ == 0)
{
lean_object* v_tail_2562_; 
v_tail_2562_ = lean_ctor_get(v_as_2550_, 1);
lean_inc(v_tail_2562_);
lean_dec_ref_known(v_as_2550_, 2);
v_as_2550_ = v_tail_2562_;
goto _start;
}
else
{
lean_object* v_head_2564_; lean_object* v_tail_2565_; lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v_inheritedTraceOptions_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_head_2564_ = lean_ctor_get(v_as_2550_, 0);
lean_inc(v_head_2564_);
v_tail_2565_ = lean_ctor_get(v_as_2550_, 1);
lean_inc(v_tail_2565_);
lean_dec_ref_known(v_as_2550_, 2);
v_fst_2566_ = lean_ctor_get(v_head_2564_, 0);
lean_inc_n(v_fst_2566_, 2);
v_snd_2567_ = lean_ctor_get(v_head_2564_, 1);
lean_inc(v_snd_2567_);
lean_dec(v_head_2564_);
v_inheritedTraceOptions_2568_ = lean_ctor_get(v___y_2555_, 13);
v___x_2569_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2570_ = l_Lean_Name_append(v___x_2569_, v_fst_2566_);
v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2568_, v_options_2560_, v___x_2570_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec(v_snd_2567_);
lean_dec(v_fst_2566_);
v_as_2550_ = v_tail_2565_;
goto _start;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_snd_2567_);
v___x_2574_ = l_Lean_MessageData_ofFormat(v___x_2573_);
v___x_2575_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2566_, v___x_2574_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_dec_ref_known(v___x_2575_, 1);
v_as_2550_ = v_tail_2565_;
goto _start;
}
else
{
lean_dec(v_tail_2565_);
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2586_, lean_object* v_i_2587_, lean_object* v_k_2588_){
_start:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_array_get_size(v_keys_2586_);
v___x_2590_ = lean_nat_dec_lt(v_i_2587_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_dec(v_i_2587_);
return v___x_2590_;
}
else
{
lean_object* v_k_x27_2591_; uint8_t v___x_2592_; 
v_k_x27_2591_ = lean_array_fget_borrowed(v_keys_2586_, v_i_2587_);
v___x_2592_ = l_Lean_instBEqExtraModUse_beq(v_k_2588_, v_k_x27_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_add(v_i_2587_, v___x_2593_);
lean_dec(v_i_2587_);
v_i_2587_ = v___x_2594_;
goto _start;
}
else
{
lean_dec(v_i_2587_);
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2596_, lean_object* v_i_2597_, lean_object* v_k_2598_){
_start:
{
uint8_t v_res_2599_; lean_object* v_r_2600_; 
v_res_2599_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2596_, v_i_2597_, v_k_2598_);
lean_dec_ref(v_k_2598_);
lean_dec_ref(v_keys_2596_);
v_r_2600_ = lean_box(v_res_2599_);
return v_r_2600_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2601_, size_t v_x_2602_, lean_object* v_x_2603_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
lean_object* v_es_2604_; lean_object* v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v_j_2608_; lean_object* v___x_2609_; 
v_es_2604_ = lean_ctor_get(v_x_2601_, 0);
v___x_2605_ = lean_box(2);
v___x_2606_ = ((size_t)31ULL);
v___x_2607_ = lean_usize_land(v_x_2602_, v___x_2606_);
v_j_2608_ = lean_usize_to_nat(v___x_2607_);
v___x_2609_ = lean_array_get_borrowed(v___x_2605_, v_es_2604_, v_j_2608_);
lean_dec(v_j_2608_);
switch(lean_obj_tag(v___x_2609_))
{
case 0:
{
lean_object* v_key_2610_; uint8_t v___x_2611_; 
v_key_2610_ = lean_ctor_get(v___x_2609_, 0);
v___x_2611_ = l_Lean_instBEqExtraModUse_beq(v_x_2603_, v_key_2610_);
return v___x_2611_;
}
case 1:
{
lean_object* v_node_2612_; size_t v___x_2613_; size_t v___x_2614_; 
v_node_2612_ = lean_ctor_get(v___x_2609_, 0);
v___x_2613_ = ((size_t)5ULL);
v___x_2614_ = lean_usize_shift_right(v_x_2602_, v___x_2613_);
v_x_2601_ = v_node_2612_;
v_x_2602_ = v___x_2614_;
goto _start;
}
default: 
{
uint8_t v___x_2616_; 
v___x_2616_ = 0;
return v___x_2616_;
}
}
}
else
{
lean_object* v_ks_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_ks_2617_ = lean_ctor_get(v_x_2601_, 0);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2617_, v___x_2618_, v_x_2603_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
size_t v_x_14855__boxed_2623_; uint8_t v_res_2624_; lean_object* v_r_2625_; 
v_x_14855__boxed_2623_ = lean_unbox_usize(v_x_2621_);
lean_dec(v_x_2621_);
v_res_2624_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2620_, v_x_14855__boxed_2623_, v_x_2622_);
lean_dec_ref(v_x_2622_);
lean_dec_ref(v_x_2620_);
v_r_2625_ = lean_box(v_res_2624_);
return v_r_2625_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
uint64_t v___x_2628_; size_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2628_ = l_Lean_instHashableExtraModUse_hash(v_x_2627_);
v___x_2629_ = lean_uint64_to_usize(v___x_2628_);
v___x_2630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2626_, v___x_2629_, v_x_2627_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2631_, v_x_2632_);
lean_dec_ref(v_x_2632_);
lean_dec_ref(v_x_2631_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1));
v___x_2638_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0));
v___x_2639_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2640_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
return v___x_2644_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__4);
v___x_2646_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
lean_ctor_set(v___x_2646_, 3, v___x_2645_);
lean_ctor_set(v___x_2646_, 4, v___x_2645_);
lean_ctor_set(v___x_2646_, 5, v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_cls_2658_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2659_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2660_ = l_Lean_Name_append(v___x_2659_, v_cls_2658_);
return v___x_2660_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___x_2666_ = l_Lean_stringToMessageData(v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2671_, uint8_t v_isMeta_2672_, lean_object* v_hint_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; lean_object* v_env_2682_; uint8_t v_isExporting_2683_; lean_object* v___x_2684_; lean_object* v_env_2685_; lean_object* v___x_2686_; lean_object* v_entry_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___x_2733_; uint8_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2681_ = lean_st_ref_get(v___y_2679_);
v_env_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc_ref(v_env_2682_);
lean_dec(v___x_2681_);
v_isExporting_2683_ = lean_ctor_get_uint8(v_env_2682_, sizeof(void*)*8);
lean_dec_ref(v_env_2682_);
v___x_2684_ = lean_st_ref_get(v___y_2679_);
v_env_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc_ref(v_env_2685_);
lean_dec(v___x_2684_);
v___x_2686_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
lean_inc(v_mod_2671_);
v_entry_2687_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2687_, 0, v_mod_2671_);
lean_ctor_set_uint8(v_entry_2687_, sizeof(void*)*1, v_isExporting_2683_);
lean_ctor_set_uint8(v_entry_2687_, sizeof(void*)*1 + 1, v_isMeta_2672_);
v___x_2688_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2689_ = lean_box(1);
v___x_2690_ = lean_box(0);
v___x_2733_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2686_, v___x_2688_, v_env_2685_, v___x_2689_, v___x_2690_);
v___x_2734_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2733_, v_entry_2687_);
lean_dec(v___x_2733_);
v___x_2735_ = lean_bool_not(v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec_ref_known(v_entry_2687_, 1);
lean_dec(v_hint_2673_);
lean_dec(v_mod_2671_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
else
{
lean_object* v_options_2738_; uint8_t v_hasTrace_2739_; 
v_options_2738_ = lean_ctor_get(v___y_2678_, 2);
v_hasTrace_2739_ = lean_ctor_get_uint8(v_options_2738_, sizeof(void*)*1);
if (v_hasTrace_2739_ == 0)
{
lean_dec(v_hint_2673_);
lean_dec(v_mod_2671_);
v___y_2692_ = v___y_2677_;
v___y_2693_ = v___y_2679_;
goto v___jp_2691_;
}
else
{
lean_object* v_inheritedTraceOptions_2740_; lean_object* v_cls_2741_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_inheritedTraceOptions_2740_ = lean_ctor_get(v___y_2678_, 13);
v_cls_2741_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2761_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14);
v___x_2762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2740_, v_options_2738_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_dec(v_hint_2673_);
lean_dec(v_mod_2671_);
v___y_2692_ = v___y_2677_;
v___y_2693_ = v___y_2679_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2763_; lean_object* v___y_2765_; 
v___x_2763_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16);
if (v_isExporting_2683_ == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__21));
v___y_2765_ = v___x_2772_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2773_; 
v___x_2773_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__22));
v___y_2765_ = v___x_2773_;
goto v___jp_2764_;
}
v___jp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_inc_ref(v___y_2765_);
v___x_2766_ = l_Lean_stringToMessageData(v___y_2765_);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2763_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
if (v_isMeta_2672_ == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2748_ = v___x_2769_;
v___y_2749_ = v___x_2770_;
goto v___jp_2747_;
}
else
{
lean_object* v___x_2771_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__20));
v___y_2748_ = v___x_2769_;
v___y_2749_ = v___x_2771_;
goto v___jp_2747_;
}
}
}
v___jp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___y_2743_);
lean_ctor_set(v___x_2745_, 1, v___y_2744_);
v___x_2746_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2741_, v___x_2745_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_dec_ref_known(v___x_2746_, 1);
v___y_2692_ = v___y_2677_;
v___y_2693_ = v___y_2679_;
goto v___jp_2691_;
}
else
{
lean_dec_ref_known(v_entry_2687_, 1);
return v___x_2746_;
}
}
v___jp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
lean_inc_ref(v___y_2749_);
v___x_2750_ = l_Lean_stringToMessageData(v___y_2749_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___y_2748_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_MessageData_ofName(v_mod_2671_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_Name_isAnonymous(v_hint_2673_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12);
v___x_2758_ = l_Lean_MessageData_ofName(v_hint_2673_);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___y_2743_ = v___x_2755_;
v___y_2744_ = v___x_2759_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2760_; 
lean_dec(v_hint_2673_);
v___x_2760_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
v___y_2743_ = v___x_2755_;
v___y_2744_ = v___x_2760_;
goto v___jp_2742_;
}
}
}
}
v___jp_2691_:
{
lean_object* v___x_2694_; lean_object* v_toEnvExtension_2695_; lean_object* v_env_2696_; lean_object* v_nextMacroScope_2697_; lean_object* v_ngen_2698_; lean_object* v_auxDeclNGen_2699_; lean_object* v_traceState_2700_; lean_object* v_messages_2701_; lean_object* v_infoState_2702_; lean_object* v_snapshotTasks_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2731_; 
v___x_2694_ = lean_st_ref_take(v___y_2693_);
v_toEnvExtension_2695_ = lean_ctor_get(v___x_2688_, 0);
v_env_2696_ = lean_ctor_get(v___x_2694_, 0);
v_nextMacroScope_2697_ = lean_ctor_get(v___x_2694_, 1);
v_ngen_2698_ = lean_ctor_get(v___x_2694_, 2);
v_auxDeclNGen_2699_ = lean_ctor_get(v___x_2694_, 3);
v_traceState_2700_ = lean_ctor_get(v___x_2694_, 4);
v_messages_2701_ = lean_ctor_get(v___x_2694_, 6);
v_infoState_2702_ = lean_ctor_get(v___x_2694_, 7);
v_snapshotTasks_2703_ = lean_ctor_get(v___x_2694_, 8);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v___x_2694_, 5);
lean_dec(v_unused_2732_);
v___x_2705_ = v___x_2694_;
v_isShared_2706_ = v_isSharedCheck_2731_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snapshotTasks_2703_);
lean_inc(v_infoState_2702_);
lean_inc(v_messages_2701_);
lean_inc(v_traceState_2700_);
lean_inc(v_auxDeclNGen_2699_);
lean_inc(v_ngen_2698_);
lean_inc(v_nextMacroScope_2697_);
lean_inc(v_env_2696_);
lean_dec(v___x_2694_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2731_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_asyncMode_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v_asyncMode_2707_ = lean_ctor_get(v_toEnvExtension_2695_, 2);
v___x_2708_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2688_, v_env_2696_, v_entry_2687_, v_asyncMode_2707_, v___x_2690_);
v___x_2709_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 5, v___x_2709_);
lean_ctor_set(v___x_2705_, 0, v___x_2708_);
v___x_2711_ = v___x_2705_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_nextMacroScope_2697_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_ngen_2698_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_auxDeclNGen_2699_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_traceState_2700_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_messages_2701_);
lean_ctor_set(v_reuseFailAlloc_2730_, 7, v_infoState_2702_);
lean_ctor_set(v_reuseFailAlloc_2730_, 8, v_snapshotTasks_2703_);
v___x_2711_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v_mctx_2714_; lean_object* v_zetaDeltaFVarIds_2715_; lean_object* v_postponed_2716_; lean_object* v_diag_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2728_; 
v___x_2712_ = lean_st_ref_set(v___y_2693_, v___x_2711_);
v___x_2713_ = lean_st_ref_take(v___y_2692_);
v_mctx_2714_ = lean_ctor_get(v___x_2713_, 0);
v_zetaDeltaFVarIds_2715_ = lean_ctor_get(v___x_2713_, 2);
v_postponed_2716_ = lean_ctor_get(v___x_2713_, 3);
v_diag_2717_ = lean_ctor_get(v___x_2713_, 4);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2713_, 1);
lean_dec(v_unused_2729_);
v___x_2719_ = v___x_2713_;
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_diag_2717_);
lean_inc(v_postponed_2716_);
lean_inc(v_zetaDeltaFVarIds_2715_);
lean_inc(v_mctx_2714_);
lean_dec(v___x_2713_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2728_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 1, v___x_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_mctx_2714_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_zetaDeltaFVarIds_2715_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v_postponed_2716_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_diag_2717_);
v___x_2723_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_st_ref_set(v___y_2692_, v___x_2723_);
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2774_, lean_object* v_isMeta_2775_, lean_object* v_hint_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_isMeta_boxed_2784_; lean_object* v_res_2785_; 
v_isMeta_boxed_2784_ = lean_unbox(v_isMeta_2775_);
v_res_2785_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2774_, v_isMeta_boxed_2784_, v_hint_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2786_, lean_object* v_declName_2787_, lean_object* v_as_2788_, size_t v_sz_2789_, size_t v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_lt(v_i_2790_, v_sz_2789_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec(v_declName_2787_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_b_2791_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; lean_object* v_modules_2802_; lean_object* v___x_2803_; lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v_toImport_2806_; lean_object* v_module_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2801_ = l_Lean_Environment_header(v___x_2786_);
v_modules_2802_ = lean_ctor_get(v___x_2801_, 3);
lean_inc_ref(v_modules_2802_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2804_ = lean_array_uget_borrowed(v_as_2788_, v_i_2790_);
v___x_2805_ = lean_array_get(v___x_2803_, v_modules_2802_, v_a_2804_);
lean_dec_ref(v_modules_2802_);
v_toImport_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_ref(v_toImport_2806_);
lean_dec(v___x_2805_);
v_module_2807_ = lean_ctor_get(v_toImport_2806_, 0);
lean_inc(v_module_2807_);
lean_dec_ref(v_toImport_2806_);
v___x_2808_ = 0;
lean_inc(v_declName_2787_);
v___x_2809_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2807_, v___x_2808_, v_declName_2787_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = lean_box(0);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2790_, v___x_2811_);
v_i_2790_ = v___x_2812_;
v_b_2791_ = v___x_2810_;
goto _start;
}
else
{
lean_dec(v_declName_2787_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2814_, lean_object* v_declName_2815_, lean_object* v_as_2816_, lean_object* v_sz_2817_, lean_object* v_i_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
size_t v_sz_boxed_2827_; size_t v_i_boxed_2828_; lean_object* v_res_2829_; 
v_sz_boxed_2827_ = lean_unbox_usize(v_sz_2817_);
lean_dec(v_sz_2817_);
v_i_boxed_2828_ = lean_unbox_usize(v_i_2818_);
lean_dec(v_i_2818_);
v_res_2829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2814_, v_declName_2815_, v_as_2816_, v_sz_boxed_2827_, v_i_boxed_2828_, v_b_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_as_2816_);
lean_dec_ref(v___x_2814_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_a_2830_, lean_object* v_x_2831_){
_start:
{
if (lean_obj_tag(v_x_2831_) == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_box(0);
return v___x_2832_;
}
else
{
lean_object* v_key_2833_; lean_object* v_value_2834_; lean_object* v_tail_2835_; uint8_t v___x_2836_; 
v_key_2833_ = lean_ctor_get(v_x_2831_, 0);
v_value_2834_ = lean_ctor_get(v_x_2831_, 1);
v_tail_2835_ = lean_ctor_get(v_x_2831_, 2);
v___x_2836_ = lean_name_eq(v_key_2833_, v_a_2830_);
if (v___x_2836_ == 0)
{
v_x_2831_ = v_tail_2835_;
goto _start;
}
else
{
lean_object* v___x_2838_; 
lean_inc(v_value_2834_);
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_value_2834_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_a_2839_, lean_object* v_x_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2839_, v_x_2840_);
lean_dec(v_x_2840_);
lean_dec(v_a_2839_);
return v_res_2841_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2842_; uint64_t v___x_2843_; 
v___x_2842_ = lean_unsigned_to_nat(1723u);
v___x_2843_ = lean_uint64_of_nat(v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_buckets_2846_; lean_object* v___x_2847_; uint64_t v___y_2849_; 
v_buckets_2846_ = lean_ctor_get(v_m_2844_, 1);
v___x_2847_ = lean_array_get_size(v_buckets_2846_);
if (lean_obj_tag(v_a_2845_) == 0)
{
uint64_t v___x_2863_; 
v___x_2863_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___closed__0);
v___y_2849_ = v___x_2863_;
goto v___jp_2848_;
}
else
{
uint64_t v_hash_2864_; 
v_hash_2864_ = lean_ctor_get_uint64(v_a_2845_, sizeof(void*)*2);
v___y_2849_ = v_hash_2864_;
goto v___jp_2848_;
}
v___jp_2848_:
{
uint64_t v___x_2850_; uint64_t v___x_2851_; uint64_t v_fold_2852_; uint64_t v___x_2853_; uint64_t v___x_2854_; uint64_t v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2850_ = 32ULL;
v___x_2851_ = lean_uint64_shift_right(v___y_2849_, v___x_2850_);
v_fold_2852_ = lean_uint64_xor(v___y_2849_, v___x_2851_);
v___x_2853_ = 16ULL;
v___x_2854_ = lean_uint64_shift_right(v_fold_2852_, v___x_2853_);
v___x_2855_ = lean_uint64_xor(v_fold_2852_, v___x_2854_);
v___x_2856_ = lean_uint64_to_usize(v___x_2855_);
v___x_2857_ = lean_usize_of_nat(v___x_2847_);
v___x_2858_ = ((size_t)1ULL);
v___x_2859_ = lean_usize_sub(v___x_2857_, v___x_2858_);
v___x_2860_ = lean_usize_land(v___x_2856_, v___x_2859_);
v___x_2861_ = lean_array_uget_borrowed(v_buckets_2846_, v___x_2860_);
v___x_2862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2845_, v___x_2861_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_m_2865_);
return v_res_2867_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___x_2871_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0));
v___x_2872_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2871_, v___x_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_2875_, uint8_t v_isMeta_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_env_2888_; lean_object* v___y_2890_; lean_object* v___x_2903_; 
v___x_2884_ = lean_st_ref_get(v___y_2882_);
v_env_2888_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_env_2888_);
lean_dec(v___x_2884_);
v___x_2903_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2888_, v_declName_2875_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_dec_ref(v_env_2888_);
lean_dec(v_declName_2875_);
goto v___jp_2885_;
}
else
{
lean_object* v_val_2904_; lean_object* v___x_2905_; lean_object* v_modules_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_val_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l_Lean_Environment_header(v_env_2888_);
v_modules_2906_ = lean_ctor_get(v___x_2905_, 3);
lean_inc_ref(v_modules_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = lean_array_get_size(v_modules_2906_);
v___x_2908_ = lean_nat_dec_lt(v_val_2904_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_dec_ref(v_modules_2906_);
lean_dec(v_val_2904_);
lean_dec_ref(v_env_2888_);
lean_dec(v_declName_2875_);
goto v___jp_2885_;
}
else
{
lean_object* v___x_2909_; lean_object* v_env_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___y_2914_; 
v___x_2909_ = lean_st_ref_get(v___y_2882_);
v_env_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_ref(v_env_2910_);
lean_dec(v___x_2909_);
v___x_2911_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__2);
v___x_2912_ = lean_array_fget(v_modules_2906_, v_val_2904_);
lean_dec(v_val_2904_);
lean_dec_ref(v_modules_2906_);
if (v_isMeta_2876_ == 0)
{
lean_dec_ref(v_env_2910_);
v___y_2914_ = v_isMeta_2876_;
goto v___jp_2913_;
}
else
{
uint8_t v___x_2925_; uint8_t v___x_2926_; 
lean_inc(v_declName_2875_);
v___x_2925_ = l_Lean_isMarkedMeta(v_env_2910_, v_declName_2875_);
v___x_2926_ = lean_bool_not(v___x_2925_);
v___y_2914_ = v___x_2926_;
goto v___jp_2913_;
}
v___jp_2913_:
{
lean_object* v_toImport_2915_; lean_object* v_module_2916_; lean_object* v___x_2917_; 
v_toImport_2915_ = lean_ctor_get(v___x_2912_, 0);
lean_inc_ref(v_toImport_2915_);
lean_dec(v___x_2912_);
v_module_2916_ = lean_ctor_get(v_toImport_2915_, 0);
lean_inc(v_module_2916_);
lean_dec_ref(v_toImport_2915_);
lean_inc(v_declName_2875_);
v___x_2917_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2916_, v___y_2914_, v_declName_2875_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec_ref_known(v___x_2917_, 1);
v___x_2918_ = l_Lean_indirectModUseExt;
v___x_2919_ = lean_box(1);
v___x_2920_ = lean_box(0);
lean_inc_ref(v_env_2888_);
v___x_2921_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2911_, v___x_2918_, v_env_2888_, v___x_2919_, v___x_2920_);
v___x_2922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_2921_, v_declName_2875_);
lean_dec(v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__3));
v___y_2890_ = v___x_2923_;
goto v___jp_2889_;
}
else
{
lean_object* v_val_2924_; 
v_val_2924_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v___x_2922_, 1);
v___y_2890_ = v_val_2924_;
goto v___jp_2889_;
}
}
else
{
lean_dec_ref(v_env_2888_);
lean_dec(v_declName_2875_);
return v___x_2917_;
}
}
}
}
v___jp_2885_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
v___jp_2889_:
{
lean_object* v___x_2891_; size_t v_sz_2892_; size_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_box(0);
v_sz_2892_ = lean_array_size(v___y_2890_);
v___x_2893_ = ((size_t)0ULL);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_2888_, v_declName_2875_, v___y_2890_, v_sz_2892_, v___x_2893_, v___x_2891_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v_env_2888_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2902_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2891_);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2891_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
return v___x_2894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_2927_, lean_object* v_isMeta_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_isMeta_boxed_2936_; lean_object* v_res_2937_; 
v_isMeta_boxed_2936_ = lean_unbox(v_isMeta_2928_);
v_res_2937_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_2927_, v_isMeta_boxed_2936_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
if (lean_obj_tag(v_as_x27_2938_) == 0)
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_b_2939_);
return v___x_2947_;
}
else
{
lean_object* v_head_2948_; lean_object* v_tail_2949_; uint8_t v___x_2950_; lean_object* v___x_2951_; 
v_head_2948_ = lean_ctor_get(v_as_x27_2938_, 0);
v_tail_2949_ = lean_ctor_get(v_as_x27_2938_, 1);
v___x_2950_ = 1;
lean_inc(v_head_2948_);
v___x_2951_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_2948_, v___x_2950_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v___x_2952_; 
lean_dec_ref_known(v___x_2951_, 1);
v___x_2952_ = lean_box(0);
v_as_x27_2938_ = v_tail_2949_;
v_b_2939_ = v___x_2952_;
goto _start;
}
else
{
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_2954_, v_b_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_as_x27_2954_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_2964_, lean_object* v_options_2965_, lean_object* v_currNamespace_2966_, lean_object* v_openDecls_2967_, lean_object* v_n_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = l_Lean_ResolveName_resolveGlobalName(v_env_2964_, v_options_2965_, v_currNamespace_2966_, v_openDecls_2967_, v_n_2968_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v___y_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_2973_, lean_object* v_options_2974_, lean_object* v_currNamespace_2975_, lean_object* v_openDecls_2976_, lean_object* v_n_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_2973_, v_options_2974_, v_currNamespace_2975_, v_openDecls_2976_, v_n_2977_, v___y_2978_, v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_options_2974_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_env_2981_, lean_object* v_currNamespace_2982_, lean_object* v_openDecls_2983_, lean_object* v_n_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_ResolveName_resolveNamespace(v_env_2981_, v_currNamespace_2982_, v_openDecls_2983_, v_n_2984_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___y_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_env_2989_, lean_object* v_currNamespace_2990_, lean_object* v_openDecls_2991_, lean_object* v_n_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_env_2989_, v_currNamespace_2990_, v_openDecls_2991_, v_n_2992_, v___y_2993_, v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2995_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v___x_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_3003_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = l_Lean_maxRecDepthErrorMessage;
v___x_3010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_3012_ = l_Lean_MessageData_ofFormat(v___x_3011_);
return v___x_3012_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_3014_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_3015_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v___x_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_ref_3016_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v_env_3034_; lean_object* v_options_3035_; lean_object* v_currRecDepth_3036_; lean_object* v_maxRecDepth_3037_; lean_object* v_ref_3038_; lean_object* v_currNamespace_3039_; lean_object* v_openDecls_3040_; lean_object* v_quotContext_3041_; lean_object* v_currMacroScope_3042_; lean_object* v___x_3043_; lean_object* v_nextMacroScope_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v_methods_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3033_ = lean_st_ref_get(v___y_3031_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref_n(v_env_3034_, 4);
lean_dec(v___x_3033_);
v_options_3035_ = lean_ctor_get(v___y_3030_, 2);
v_currRecDepth_3036_ = lean_ctor_get(v___y_3030_, 3);
v_maxRecDepth_3037_ = lean_ctor_get(v___y_3030_, 4);
v_ref_3038_ = lean_ctor_get(v___y_3030_, 5);
v_currNamespace_3039_ = lean_ctor_get(v___y_3030_, 6);
v_openDecls_3040_ = lean_ctor_get(v___y_3030_, 7);
v_quotContext_3041_ = lean_ctor_get(v___y_3030_, 10);
v_currMacroScope_3042_ = lean_ctor_get(v___y_3030_, 11);
v___x_3043_ = lean_st_ref_get(v___y_3031_);
v_nextMacroScope_3044_ = lean_ctor_get(v___x_3043_, 1);
lean_inc(v_nextMacroScope_3044_);
lean_dec(v___x_3043_);
v___f_3045_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3045_, 0, v_env_3034_);
v___f_3046_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3046_, 0, v_env_3034_);
lean_inc_n(v_openDecls_3040_, 2);
lean_inc_n(v_currNamespace_3039_, 3);
v___f_3047_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3047_, 0, v_env_3034_);
lean_closure_set(v___f_3047_, 1, v_currNamespace_3039_);
lean_closure_set(v___f_3047_, 2, v_openDecls_3040_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3048_, 0, v_currNamespace_3039_);
lean_inc_ref(v_options_3035_);
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3049_, 0, v_env_3034_);
lean_closure_set(v___f_3049_, 1, v_options_3035_);
lean_closure_set(v___f_3049_, 2, v_currNamespace_3039_);
lean_closure_set(v___f_3049_, 3, v_openDecls_3040_);
v_methods_3050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3050_, 0, v___f_3045_);
lean_ctor_set(v_methods_3050_, 1, v___f_3048_);
lean_ctor_set(v_methods_3050_, 2, v___f_3046_);
lean_ctor_set(v_methods_3050_, 3, v___f_3047_);
lean_ctor_set(v_methods_3050_, 4, v___f_3049_);
lean_inc(v_ref_3038_);
lean_inc(v_maxRecDepth_3037_);
lean_inc(v_currRecDepth_3036_);
lean_inc(v_currMacroScope_3042_);
lean_inc(v_quotContext_3041_);
v___x_3051_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3051_, 0, v_methods_3050_);
lean_ctor_set(v___x_3051_, 1, v_quotContext_3041_);
lean_ctor_set(v___x_3051_, 2, v_currMacroScope_3042_);
lean_ctor_set(v___x_3051_, 3, v_currRecDepth_3036_);
lean_ctor_set(v___x_3051_, 4, v_maxRecDepth_3037_);
lean_ctor_set(v___x_3051_, 5, v_ref_3038_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3053_, 0, v_nextMacroScope_3044_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
v___x_3054_ = lean_apply_2(v_x_3025_, v___x_3051_, v___x_3053_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v_a_3056_; lean_object* v_macroScope_3057_; lean_object* v_traceMsgs_3058_; lean_object* v_expandedMacroDecls_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 1);
lean_inc(v_a_3055_);
v_a_3056_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3054_, 2);
v_macroScope_3057_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_macroScope_3057_);
v_traceMsgs_3058_ = lean_ctor_get(v_a_3055_, 1);
lean_inc(v_traceMsgs_3058_);
v_expandedMacroDecls_3059_ = lean_ctor_get(v_a_3055_, 2);
lean_inc(v_expandedMacroDecls_3059_);
lean_dec(v_a_3055_);
v___x_3060_ = lean_box(0);
v___x_3061_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_3059_, v___x_3060_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v_expandedMacroDecls_3059_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; lean_object* v_env_3063_; lean_object* v_ngen_3064_; lean_object* v_auxDeclNGen_3065_; lean_object* v_traceState_3066_; lean_object* v_cache_3067_; lean_object* v_messages_3068_; lean_object* v_infoState_3069_; lean_object* v_snapshotTasks_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref_known(v___x_3061_, 1);
v___x_3062_ = lean_st_ref_take(v___y_3031_);
v_env_3063_ = lean_ctor_get(v___x_3062_, 0);
v_ngen_3064_ = lean_ctor_get(v___x_3062_, 2);
v_auxDeclNGen_3065_ = lean_ctor_get(v___x_3062_, 3);
v_traceState_3066_ = lean_ctor_get(v___x_3062_, 4);
v_cache_3067_ = lean_ctor_get(v___x_3062_, 5);
v_messages_3068_ = lean_ctor_get(v___x_3062_, 6);
v_infoState_3069_ = lean_ctor_get(v___x_3062_, 7);
v_snapshotTasks_3070_ = lean_ctor_get(v___x_3062_, 8);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v___x_3062_, 1);
lean_dec(v_unused_3097_);
v___x_3072_ = v___x_3062_;
v_isShared_3073_ = v_isSharedCheck_3096_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_snapshotTasks_3070_);
lean_inc(v_infoState_3069_);
lean_inc(v_messages_3068_);
lean_inc(v_cache_3067_);
lean_inc(v_traceState_3066_);
lean_inc(v_auxDeclNGen_3065_);
lean_inc(v_ngen_3064_);
lean_inc(v_env_3063_);
lean_dec(v___x_3062_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3096_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v_macroScope_3057_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_env_3063_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_macroScope_3057_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_ngen_3064_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_auxDeclNGen_3065_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_traceState_3066_);
lean_ctor_set(v_reuseFailAlloc_3095_, 5, v_cache_3067_);
lean_ctor_set(v_reuseFailAlloc_3095_, 6, v_messages_3068_);
lean_ctor_set(v_reuseFailAlloc_3095_, 7, v_infoState_3069_);
lean_ctor_set(v_reuseFailAlloc_3095_, 8, v_snapshotTasks_3070_);
v___x_3075_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_st_ref_set(v___y_3031_, v___x_3075_);
v___x_3077_ = l_List_reverse___redArg(v_traceMsgs_3058_);
v___x_3078_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3077_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___x_3078_, 0);
lean_dec(v_unused_3086_);
v___x_3080_ = v___x_3078_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_dec(v___x_3078_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v_a_3056_);
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3056_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_a_3056_);
v_a_3087_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3078_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3078_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_traceMsgs_3058_);
lean_dec(v_macroScope_3057_);
lean_dec(v_a_3056_);
v_a_3098_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3061_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3061_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3054_, 2);
if (lean_obj_tag(v_a_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v_a_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v_a_3107_ = lean_ctor_get(v_a_3106_, 0);
lean_inc(v_a_3107_);
v_a_3108_ = lean_ctor_get(v_a_3106_, 1);
lean_inc_ref(v_a_3108_);
lean_dec_ref_known(v_a_3106_, 2);
v___x_3109_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3110_ = lean_string_dec_eq(v_a_3108_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3111_, 0, v_a_3108_);
v___x_3112_ = l_Lean_MessageData_ofFormat(v___x_3111_);
v___x_3113_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3107_, v___x_3112_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v_a_3107_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
lean_dec_ref(v_a_3108_);
v___x_3114_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3107_);
return v___x_3114_;
}
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3125_, lean_object* v_binders_3126_, lean_object* v_type_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___y_3136_; lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_inc_ref(v_pre_3125_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3140_, 0, v_type_3127_);
lean_closure_set(v___f_3140_, 1, v_pre_3125_);
v___x_3141_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3141_, 0, lean_box(0));
lean_closure_set(v___x_3141_, 1, v_binders_3126_);
lean_closure_set(v___x_3141_, 2, v___f_3140_);
v___x_3142_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3141_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_dec_ref(v_pre_3125_);
v___y_3136_ = v___x_3142_;
goto v___jp_3135_;
}
else
{
lean_object* v_a_3143_; uint8_t v___y_3145_; uint8_t v___x_3149_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
v___x_3149_ = l_Lean_Exception_isInterrupt(v_a_3143_);
if (v___x_3149_ == 0)
{
uint8_t v___x_3150_; 
v___x_3150_ = l_Lean_Exception_isRuntime(v_a_3143_);
v___y_3145_ = v___x_3150_;
goto v___jp_3144_;
}
else
{
lean_dec(v_a_3143_);
v___y_3145_ = v___x_3149_;
goto v___jp_3144_;
}
v___jp_3144_:
{
if (v___y_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec_ref_known(v___x_3142_, 1);
v___x_3146_ = lean_box(0);
v___x_3147_ = l_Lean_Name_str___override(v___x_3146_, v_pre_3125_);
v___x_3148_ = l_Lean_Core_mkFreshUserName(v___x_3147_, v_a_3132_, v_a_3133_);
v___y_3136_ = v___x_3148_;
goto v___jp_3135_;
}
else
{
lean_dec_ref(v_pre_3125_);
v___y_3136_ = v___x_3142_;
goto v___jp_3135_;
}
}
}
v___jp_3135_:
{
if (lean_obj_tag(v___y_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_a_3137_ = lean_ctor_get(v___y_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___y_3136_, 1);
v___x_3138_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3138_, 0, v_a_3137_);
v___x_3139_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3138_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3139_;
}
else
{
return v___y_3136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3151_, lean_object* v_binders_3152_, lean_object* v_type_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3151_, v_binders_3152_, v_type_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3162_, lean_object* v_x_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3163_, v___y_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3167_, v_x_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v_x_3168_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3172_, lean_object* v_ref_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3173_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_ref_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3182_, v_ref_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3210_, lean_object* v_x_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3220_, v_x_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3230_, lean_object* v_msg_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3230_, v_msg_3231_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3240_, lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3240_, v_msg_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3250_, lean_object* v_as_x27_3251_, lean_object* v_b_3252_, lean_object* v_a_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3251_, v_b_3252_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3262_, lean_object* v_as_x27_3263_, lean_object* v_b_3264_, lean_object* v_a_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3262_, v_as_x27_3263_, v_b_3264_, v_a_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v_as_x27_3263_);
lean_dec(v_as_3262_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3274_, lean_object* v_ref_3275_, lean_object* v_msg_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3275_, v_msg_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_ref_3286_, lean_object* v_msg_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3285_, v_ref_3286_, v_msg_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v_ref_3286_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3296_, lean_object* v_m_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3297_, v_a_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3300_, lean_object* v_m_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3300_, v_m_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_m_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3304_, lean_object* v_msg_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_msg_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3314_, v_msg_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_){
_start:
{
uint8_t v___x_3327_; 
v___x_3327_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3325_, v_x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3328_, v_x_3329_, v_x_3330_);
lean_dec_ref(v_x_3330_);
lean_dec_ref(v_x_3329_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3333_, lean_object* v_a_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_3334_, v_x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_a_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3337_, v_a_3338_, v_x_3339_);
lean_dec(v_x_3339_);
lean_dec(v_a_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3341_, lean_object* v_macroStack_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3341_, v_macroStack_3342_, v___y_3347_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3351_, lean_object* v_macroStack_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3351_, v_macroStack_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
return v_res_3360_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3361_, lean_object* v_x_3362_, size_t v_x_3363_, lean_object* v_x_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3362_, v_x_3363_, v_x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3366_, lean_object* v_x_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_){
_start:
{
size_t v_x_15941__boxed_3370_; uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_x_15941__boxed_3370_ = lean_unbox_usize(v_x_3368_);
lean_dec(v_x_3368_);
v_res_3371_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3366_, v_x_3367_, v_x_15941__boxed_3370_, v_x_3369_);
lean_dec_ref(v_x_3369_);
lean_dec_ref(v_x_3367_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3373_, lean_object* v_keys_3374_, lean_object* v_vals_3375_, lean_object* v_heq_3376_, lean_object* v_i_3377_, lean_object* v_k_3378_){
_start:
{
uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3374_, v_i_3377_, v_k_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3380_, lean_object* v_keys_3381_, lean_object* v_vals_3382_, lean_object* v_heq_3383_, lean_object* v_i_3384_, lean_object* v_k_3385_){
_start:
{
uint8_t v_res_3386_; lean_object* v_r_3387_; 
v_res_3386_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3380_, v_keys_3381_, v_vals_3382_, v_heq_3383_, v_i_3384_, v_k_3385_);
lean_dec_ref(v_k_3385_);
lean_dec_ref(v_vals_3382_);
lean_dec_ref(v_keys_3381_);
v_r_3387_ = lean_box(v_res_3386_);
return v_r_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3389_, lean_object* v_type_3390_, lean_object* v_x_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3400_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3399_, v_binders_3389_, v_type_3390_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3401_, lean_object* v_type_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3401_, v_type_3402_, v_x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v_x_3403_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3412_, lean_object* v_val_3413_, lean_object* v_a_x3f_3414_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_st_ref_set(v_a_3412_, v_val_3413_);
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3418_, lean_object* v_val_3419_, lean_object* v_a_x3f_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3418_, v_val_3419_, v_a_x3f_3420_);
lean_dec(v_a_x3f_3420_);
lean_dec(v_a_3418_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3423_, lean_object* v_type_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v___x_3428_; lean_object* v___f_3429_; lean_object* v_r_3430_; 
v___x_3428_ = lean_st_ref_get(v_a_3426_);
v___f_3429_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3429_, 0, v_binders_3423_);
lean_closure_set(v___f_3429_, 1, v_type_3424_);
v_r_3430_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3429_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v_r_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3447_; 
v_a_3431_ = lean_ctor_get(v_r_3430_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_r_3430_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3433_ = v_r_3430_;
v_isShared_3434_ = v_isSharedCheck_3447_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v_r_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3447_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
lean_inc(v_a_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v___x_3437_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3426_, v___x_3428_, v___x_3436_);
lean_dec_ref(v___x_3436_);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v___x_3437_, 0);
lean_dec(v_unused_3445_);
v___x_3439_ = v___x_3437_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_dec(v___x_3437_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v_a_3431_);
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3431_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3448_ = lean_ctor_get(v_r_3430_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v_r_3430_, 1);
v___x_3449_ = lean_box(0);
v___x_3450_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3426_, v___x_3428_, v___x_3449_);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3458_);
v___x_3452_ = v___x_3450_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v___x_3450_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set_tag(v___x_3452_, 1);
lean_ctor_set(v___x_3452_, 0, v_a_3448_);
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3448_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3459_, lean_object* v_type_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3459_, v_type_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
return v_res_3464_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclNameGen(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
