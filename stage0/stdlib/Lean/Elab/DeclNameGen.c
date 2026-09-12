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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
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
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_nbuckets_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_259_ = lean_array_get_size(v_data_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v_nbuckets_261_ = lean_nat_mul(v___x_259_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_box(0);
v___x_264_ = lean_mk_array(v_nbuckets_261_, v___x_263_);
v___x_265_ = lean_array_propagate_mark(v_data_258_, v___x_264_);
v___x_266_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v___x_262_, v_data_258_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(lean_object* v_a_267_, lean_object* v_b_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_dec(v_b_268_);
lean_dec_ref(v_a_267_);
return v_x_269_;
}
else
{
lean_object* v_key_270_; lean_object* v_value_271_; lean_object* v_tail_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_284_; 
v_key_270_ = lean_ctor_get(v_x_269_, 0);
v_value_271_ = lean_ctor_get(v_x_269_, 1);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_284_ == 0)
{
v___x_274_ = v_x_269_;
v_isShared_275_ = v_isSharedCheck_284_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_tail_272_);
lean_inc(v_value_271_);
lean_inc(v_key_270_);
lean_dec(v_x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_284_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___x_276_; 
v___x_276_ = lean_expr_eqv(v_key_270_, v_a_267_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_267_, v_b_268_, v_tail_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 2, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_key_270_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_value_271_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
lean_object* v___x_282_; 
lean_dec(v_value_271_);
lean_dec(v_key_270_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v_b_268_);
lean_ctor_set(v___x_274_, 0, v_a_267_);
v___x_282_ = v___x_274_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_267_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_b_268_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_tail_272_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(lean_object* v_m_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_size_288_; lean_object* v_buckets_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_332_; 
v_size_288_ = lean_ctor_get(v_m_285_, 0);
v_buckets_289_ = lean_ctor_get(v_m_285_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_m_285_);
if (v_isSharedCheck_332_ == 0)
{
v___x_291_ = v_m_285_;
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_buckets_289_);
lean_inc(v_size_288_);
lean_dec(v_m_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v_fold_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v_bkt_306_; uint8_t v___x_307_; 
v___x_293_ = lean_array_get_size(v_buckets_289_);
v___x_294_ = l_Lean_Expr_hash(v_a_286_);
v___x_295_ = 32ULL;
v___x_296_ = lean_uint64_shift_right(v___x_294_, v___x_295_);
v_fold_297_ = lean_uint64_xor(v___x_294_, v___x_296_);
v___x_298_ = 16ULL;
v___x_299_ = lean_uint64_shift_right(v_fold_297_, v___x_298_);
v___x_300_ = lean_uint64_xor(v_fold_297_, v___x_299_);
v___x_301_ = lean_uint64_to_usize(v___x_300_);
v___x_302_ = lean_usize_of_nat(v___x_293_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_sub(v___x_302_, v___x_303_);
v___x_305_ = lean_usize_land(v___x_301_, v___x_304_);
v_bkt_306_ = lean_array_uget_borrowed(v_buckets_289_, v___x_305_);
v___x_307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_286_, v_bkt_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v_size_x27_309_; lean_object* v___x_310_; lean_object* v_buckets_x27_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v_size_x27_309_ = lean_nat_add(v_size_288_, v___x_308_);
lean_dec(v_size_288_);
lean_inc(v_bkt_306_);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v_a_286_);
lean_ctor_set(v___x_310_, 1, v_b_287_);
lean_ctor_set(v___x_310_, 2, v_bkt_306_);
v_buckets_x27_311_ = lean_array_uset(v_buckets_289_, v___x_305_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v_size_x27_309_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_div(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_array_get_size(v_buckets_x27_311_);
v___x_317_ = lean_nat_dec_le(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v_val_318_; lean_object* v___x_320_; 
v_val_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_311_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_val_318_);
lean_ctor_set(v___x_291_, 0, v_size_x27_309_);
v___x_320_ = v___x_291_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_buckets_x27_311_);
lean_ctor_set(v___x_291_, 0, v_size_x27_309_);
v___x_323_ = v___x_291_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_buckets_x27_311_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v_buckets_x27_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc(v_bkt_306_);
v___x_325_ = lean_box(0);
v_buckets_x27_326_ = lean_array_uset(v_buckets_289_, v___x_305_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_286_, v_b_287_, v_bkt_306_);
v___x_328_ = lean_array_uset(v_buckets_x27_326_, v___x_305_, v___x_327_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_328_);
v___x_330_ = v___x_291_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_288_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v_key_336_; lean_object* v_value_337_; lean_object* v_tail_338_; uint8_t v___x_339_; 
v_key_336_ = lean_ctor_get(v_x_334_, 0);
v_value_337_ = lean_ctor_get(v_x_334_, 1);
v_tail_338_ = lean_ctor_get(v_x_334_, 2);
v___x_339_ = lean_expr_eqv(v_key_336_, v_a_333_);
if (v___x_339_ == 0)
{
v_x_334_ = v_tail_338_;
goto _start;
}
else
{
lean_object* v___x_341_; 
lean_inc(v_value_337_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_value_337_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg___boxed(lean_object* v_a_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_342_, v_x_343_);
lean_dec(v_x_343_);
lean_dec_ref(v_a_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_buckets_347_; lean_object* v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v_fold_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_buckets_347_ = lean_ctor_get(v_m_345_, 1);
v___x_348_ = lean_array_get_size(v_buckets_347_);
v___x_349_ = l_Lean_Expr_hash(v_a_346_);
v___x_350_ = 32ULL;
v___x_351_ = lean_uint64_shift_right(v___x_349_, v___x_350_);
v_fold_352_ = lean_uint64_xor(v___x_349_, v___x_351_);
v___x_353_ = 16ULL;
v___x_354_ = lean_uint64_shift_right(v_fold_352_, v___x_353_);
v___x_355_ = lean_uint64_xor(v_fold_352_, v___x_354_);
v___x_356_ = lean_uint64_to_usize(v___x_355_);
v___x_357_ = lean_usize_of_nat(v___x_348_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_sub(v___x_357_, v___x_358_);
v___x_360_ = lean_usize_land(v___x_356_, v___x_359_);
v___x_361_ = lean_array_uget_borrowed(v_buckets_347_, v___x_360_);
v___x_362_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_346_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg___boxed(lean_object* v_m_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_363_, v_a_364_);
lean_dec_ref(v_a_364_);
lean_dec_ref(v_m_363_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0(void){
_start:
{
lean_object* v___x_366_; lean_object* v_dummy_367_; 
v___x_366_ = lean_box(0);
v_dummy_367_ = l_Lean_Expr_sort___override(v___x_366_);
return v_dummy_367_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__0));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(lean_object* v_snd_371_, lean_object* v_args_372_, lean_object* v_a_373_, lean_object* v_____r_374_, lean_object* v_fty_375_, lean_object* v_j_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
if (lean_obj_tag(v_fty_375_) == 7)
{
lean_object* v_body_383_; uint8_t v_binderInfo_384_; lean_object* v___x_390_; uint8_t v_a_392_; uint8_t v___x_435_; 
v_body_383_ = lean_ctor_get(v_fty_375_, 2);
lean_inc_ref(v_body_383_);
v_binderInfo_384_ = lean_ctor_get_uint8(v_fty_375_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fty_375_, 3);
v___x_390_ = lean_array_fget_borrowed(v_args_372_, v_a_373_);
v___x_435_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_384_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Expr_isSort(v___x_390_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_inc(v___x_390_);
v___x_437_ = l_Lean_Meta_isTypeFormer(v___x_390_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; uint8_t v___x_439_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_unbox(v_a_438_);
lean_dec(v_a_438_);
v_a_392_ = v___x_439_;
goto v___jp_391_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_body_383_);
lean_dec(v_snd_371_);
v_a_440_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_437_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
goto v___jp_385_;
}
}
else
{
v_a_392_ = v___x_435_;
goto v___jp_391_;
}
v___jp_385_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc(v_j_376_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_j_376_);
lean_ctor_set(v___x_386_, 1, v_snd_371_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_body_383_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
v___jp_391_:
{
if (v_a_392_ == 0)
{
goto v___jp_385_;
}
else
{
lean_object* v___x_393_; 
lean_inc(v___x_390_);
v___x_393_ = l_Lean_Meta_isProof(v___x_390_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_426_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_426_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_426_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_426_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v_a_394_);
lean_dec(v_a_394_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_del_object(v___x_396_);
lean_inc(v___x_390_);
v___x_399_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_390_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_404_ = l_Lean_Expr_app___override(v_snd_371_, v_a_400_);
lean_inc(v_j_376_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_j_376_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_body_383_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_407_);
v___x_409_ = v___x_402_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_body_383_);
lean_dec(v_snd_371_);
v_a_412_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_399_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_399_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_inc(v_j_376_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_j_376_);
lean_ctor_set(v___x_420_, 1, v_snd_371_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_body_383_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_422_);
v___x_424_ = v___x_396_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_body_383_);
lean_dec(v_snd_371_);
v_a_427_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_393_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_393_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___closed__1);
v___x_449_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v___x_448_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_459_; 
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_460_);
v___x_451_ = v___x_449_;
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_449_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
lean_inc(v_j_376_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_j_376_);
lean_ctor_set(v___x_453_, 1, v_snd_371_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_fty_375_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_455_);
v___x_457_ = v___x_451_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_fty_375_);
lean_dec(v_snd_371_);
v_a_461_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_449_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_449_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(lean_object* v_upperBound_469_, lean_object* v_args_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___y_480_; uint8_t v___x_502_; 
v___x_502_ = lean_nat_dec_lt(v_a_471_, v_upperBound_469_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v_a_471_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v_b_472_);
return v___x_503_;
}
else
{
lean_object* v_snd_504_; lean_object* v_fst_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___y_509_; uint8_t v___x_521_; 
v_snd_504_ = lean_ctor_get(v_b_472_, 1);
lean_inc(v_snd_504_);
v_fst_505_ = lean_ctor_get(v_b_472_, 0);
lean_inc(v_fst_505_);
lean_dec_ref(v_b_472_);
v_fst_506_ = lean_ctor_get(v_snd_504_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v_snd_504_, 1);
lean_inc(v_snd_507_);
lean_dec(v_snd_504_);
v___x_521_ = l_Lean_Expr_isForall(v_fst_505_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; uint8_t v_transparency_523_; uint8_t v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_522_ = l_Lean_Meta_Context_config(v___y_474_);
v_transparency_523_ = lean_ctor_get_uint8(v___x_522_, 9);
lean_dec_ref(v___x_522_);
v___x_524_ = 0;
v___x_525_ = lean_expr_instantiate_rev_range(v_fst_505_, v_fst_506_, v_a_471_, v_args_470_);
lean_dec(v_fst_506_);
lean_dec(v_fst_505_);
v___x_526_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_523_, v___x_524_);
if (v___x_526_ == 0)
{
lean_object* v_keyedConfig_527_; uint8_t v_trackZetaDelta_528_; lean_object* v_zetaDeltaSet_529_; lean_object* v_lctx_530_; lean_object* v_localInstances_531_; lean_object* v_defEqCtx_x3f_532_; lean_object* v_synthPendingDepth_533_; lean_object* v_customCanUnfoldPredicate_x3f_534_; uint8_t v_univApprox_535_; uint8_t v_inTypeClassResolution_536_; uint8_t v_cacheInferType_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_keyedConfig_527_ = lean_ctor_get(v___y_474_, 0);
v_trackZetaDelta_528_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*7);
v_zetaDeltaSet_529_ = lean_ctor_get(v___y_474_, 1);
v_lctx_530_ = lean_ctor_get(v___y_474_, 2);
v_localInstances_531_ = lean_ctor_get(v___y_474_, 3);
v_defEqCtx_x3f_532_ = lean_ctor_get(v___y_474_, 4);
v_synthPendingDepth_533_ = lean_ctor_get(v___y_474_, 5);
v_customCanUnfoldPredicate_x3f_534_ = lean_ctor_get(v___y_474_, 6);
v_univApprox_535_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_536_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*7 + 2);
v_cacheInferType_537_ = lean_ctor_get_uint8(v___y_474_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_527_);
v___x_538_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_524_, v_keyedConfig_527_);
lean_inc(v_customCanUnfoldPredicate_x3f_534_);
lean_inc(v_synthPendingDepth_533_);
lean_inc(v_defEqCtx_x3f_532_);
lean_inc_ref(v_localInstances_531_);
lean_inc_ref(v_lctx_530_);
lean_inc(v_zetaDeltaSet_529_);
v___x_539_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_zetaDeltaSet_529_);
lean_ctor_set(v___x_539_, 2, v_lctx_530_);
lean_ctor_set(v___x_539_, 3, v_localInstances_531_);
lean_ctor_set(v___x_539_, 4, v_defEqCtx_x3f_532_);
lean_ctor_set(v___x_539_, 5, v_synthPendingDepth_533_);
lean_ctor_set(v___x_539_, 6, v_customCanUnfoldPredicate_x3f_534_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7, v_trackZetaDelta_528_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 1, v_univApprox_535_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 2, v_inTypeClassResolution_536_);
lean_ctor_set_uint8(v___x_539_, sizeof(void*)*7 + 3, v_cacheInferType_537_);
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
v___x_540_ = lean_whnf(v___x_525_, v___x_539_, v___y_475_, v___y_476_, v___y_477_);
v___y_509_ = v___x_540_;
goto v___jp_508_;
}
else
{
lean_object* v___x_541_; 
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
v___x_541_ = lean_whnf(v___x_525_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
v___y_509_ = v___x_541_;
goto v___jp_508_;
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(0);
v___x_543_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_507_, v_args_470_, v_a_471_, v___x_542_, v_fst_505_, v_fst_506_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v_fst_506_);
v___y_480_ = v___x_543_;
goto v___jp_479_;
}
v___jp_508_:
{
if (lean_obj_tag(v___y_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_510_ = lean_ctor_get(v___y_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___y_509_, 1);
v___x_511_ = lean_box(0);
v___x_512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_507_, v_args_470_, v_a_471_, v___x_511_, v_a_510_, v_a_471_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
v___y_480_ = v___x_512_;
goto v___jp_479_;
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_snd_507_);
lean_dec(v_a_471_);
v_a_513_ = lean_ctor_get(v___y_509_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___y_509_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___y_509_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___y_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
v___jp_479_:
{
if (lean_obj_tag(v___y_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v_a_481_ = lean_ctor_get(v___y_480_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___y_480_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v___y_480_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___y_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
if (lean_obj_tag(v_a_481_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; 
lean_dec(v_a_471_);
v_a_485_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v_a_481_, 1);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_a_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_del_object(v___x_483_);
v_a_489_ = lean_ctor_get(v_a_481_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v_a_481_, 1);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_a_471_, v___x_490_);
lean_dec(v_a_471_);
v_a_471_ = v___x_491_;
v_b_472_ = v_a_489_;
goto _start;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_a_471_);
v_a_494_ = lean_ctor_get(v___y_480_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___y_480_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___y_480_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___y_480_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
if (lean_obj_tag(v_x_544_) == 5)
{
lean_object* v_fn_553_; lean_object* v_arg_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_fn_553_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_fn_553_);
v_arg_554_ = lean_ctor_get(v_x_544_, 1);
lean_inc_ref(v_arg_554_);
lean_dec_ref_known(v_x_544_, 2);
v___x_555_ = lean_array_set(v_x_545_, v_x_546_, v_arg_554_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_sub(v_x_546_, v___x_556_);
lean_dec(v_x_546_);
v_x_544_ = v_fn_553_;
v_x_545_ = v___x_555_;
v_x_546_ = v___x_557_;
goto _start;
}
else
{
lean_object* v___x_559_; 
lean_dec(v_x_546_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc_ref(v_x_544_);
v___x_559_ = lean_infer_type(v_x_544_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_x_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = lean_array_get_size(v_x_545_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_561_);
lean_ctor_set(v___x_565_, 1, v_a_563_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_560_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v___x_564_, v_x_545_, v___x_561_, v___x_566_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec_ref(v_x_545_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_snd_572_; lean_object* v_snd_573_; lean_object* v___x_575_; 
v_snd_572_ = lean_ctor_get(v_a_568_, 1);
lean_inc(v_snd_572_);
lean_dec(v_a_568_);
v_snd_573_ = lean_ctor_get(v_snd_572_, 1);
lean_inc(v_snd_573_);
lean_dec(v_snd_572_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_snd_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_snd_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_567_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_567_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_dec(v_a_560_);
lean_dec_ref(v_x_545_);
return v___x_562_;
}
}
else
{
lean_dec_ref(v_x_545_);
lean_dec_ref(v_x_544_);
return v___x_559_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = l_Lean_Expr_bvar___override(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(lean_object* v_body_588_, lean_object* v_binderName_589_, uint8_t v_binderInfo_590_, lean_object* v_binderType_591_, lean_object* v_arg_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_ty_x27_600_; uint8_t v___x_612_; 
v___x_612_ = l_Lean_Expr_hasLooseBVars(v_body_588_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_binderType_591_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v_ty_x27_600_ = v_a_614_;
goto v___jp_599_;
}
else
{
lean_dec(v_binderName_589_);
return v___x_613_;
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref(v_binderType_591_);
v___x_615_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_ty_x27_600_ = v___x_615_;
goto v___jp_599_;
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_expr_instantiate1(v_body_588_, v_arg_592_);
v___x_602_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_601_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_Expr_forallE___override(v_binderName_589_, v_ty_x27_600_, v_a_603_, v_binderInfo_590_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_dec_ref(v_ty_x27_600_);
lean_dec(v_binderName_589_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed(lean_object* v_body_616_, lean_object* v_binderName_617_, lean_object* v_binderInfo_618_, lean_object* v_binderType_619_, lean_object* v_arg_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v_binderInfo_15860__boxed_627_; lean_object* v_res_628_; 
v_binderInfo_15860__boxed_627_ = lean_unbox(v_binderInfo_618_);
v_res_628_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0(v_body_616_, v_binderName_617_, v_binderInfo_15860__boxed_627_, v_binderType_619_, v_arg_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v_arg_620_);
lean_dec_ref(v_body_616_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed(lean_object* v_body_629_, lean_object* v_arg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(v_body_629_, v_arg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_body_629_);
return v_res_637_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__2));
v___x_642_ = l_Lean_Level_param___override(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__3);
v___x_644_ = l_Lean_Expr_sort___override(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Lean_Level_succ___override(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__5);
v___x_648_ = l_Lean_Expr_sort___override(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_a_657_; lean_object* v___y_663_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_st_ref_get(v_a_650_);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v___x_665_, v_e_649_);
lean_dec(v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; 
lean_inc_ref(v_e_649_);
v___x_667_ = l_Lean_Meta_isProof(v_e_649_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; uint8_t v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = lean_unbox(v_a_668_);
lean_dec(v_a_668_);
if (v___x_669_ == 0)
{
switch(lean_obj_tag(v_e_649_))
{
case 5:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_getParentProjArg___redArg(v_e_649_, v_a_654_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
if (lean_obj_tag(v_a_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; 
v_val_672_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_a_671_, 1);
v___x_673_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_672_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_673_;
goto v___jp_662_;
}
else
{
lean_object* v_dummy_674_; lean_object* v_nargs_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_a_671_);
v_dummy_674_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_nargs_675_ = l_Lean_Expr_getAppNumArgs(v_e_649_);
lean_inc(v_nargs_675_);
v___x_676_ = lean_mk_array(v_nargs_675_, v_dummy_674_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_sub(v_nargs_675_, v___x_677_);
lean_dec(v_nargs_675_);
lean_inc_ref(v_e_649_);
v___x_679_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_e_649_, v___x_676_, v___x_678_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_679_;
goto v___jp_662_;
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref_known(v_e_649_, 2);
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
case 7:
{
lean_object* v_binderName_688_; lean_object* v_binderType_689_; lean_object* v_body_690_; uint8_t v_binderInfo_691_; lean_object* v___x_692_; lean_object* v___f_693_; uint8_t v___x_694_; lean_object* v___x_695_; 
v_binderName_688_ = lean_ctor_get(v_e_649_, 0);
v_binderType_689_ = lean_ctor_get(v_e_649_, 1);
v_body_690_ = lean_ctor_get(v_e_649_, 2);
v_binderInfo_691_ = lean_ctor_get_uint8(v_e_649_, sizeof(void*)*3 + 8);
v___x_692_ = lean_box(v_binderInfo_691_);
lean_inc_ref_n(v_binderType_689_, 2);
lean_inc_n(v_binderName_688_, 2);
lean_inc_ref(v_body_690_);
v___f_693_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_693_, 0, v_body_690_);
lean_closure_set(v___f_693_, 1, v_binderName_688_);
lean_closure_set(v___f_693_, 2, v___x_692_);
lean_closure_set(v___f_693_, 3, v_binderType_689_);
v___x_694_ = 0;
v___x_695_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_688_, v_binderInfo_691_, v_binderType_689_, v___f_693_, v___x_694_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_695_;
goto v___jp_662_;
}
case 6:
{
lean_object* v_binderName_696_; lean_object* v_binderType_697_; lean_object* v_body_698_; uint8_t v_binderInfo_699_; lean_object* v___x_700_; 
v_binderName_696_ = lean_ctor_get(v_e_649_, 0);
v_binderType_697_ = lean_ctor_get(v_e_649_, 1);
v_body_698_ = lean_ctor_get(v_e_649_, 2);
v_binderInfo_699_ = lean_ctor_get_uint8(v_e_649_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_649_);
v___x_700_ = l_Lean_Expr_etaExpandedStrict_x3f(v_e_649_);
if (lean_obj_tag(v___x_700_) == 1)
{
lean_object* v_val_701_; lean_object* v___x_702_; 
v_val_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_val_701_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_702_;
goto v___jp_662_;
}
else
{
lean_object* v___f_703_; uint8_t v___x_704_; lean_object* v___x_705_; 
lean_dec(v___x_700_);
lean_inc_ref(v_body_698_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1___boxed), 8, 1);
lean_closure_set(v___f_703_, 0, v_body_698_);
v___x_704_ = 0;
lean_inc_ref(v_binderType_697_);
lean_inc(v_binderName_696_);
v___x_705_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__5___redArg(v_binderName_696_, v_binderInfo_699_, v_binderType_697_, v___f_703_, v___x_704_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_705_;
goto v___jp_662_;
}
}
case 8:
{
lean_object* v_value_706_; lean_object* v_body_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_value_706_ = lean_ctor_get(v_e_649_, 2);
v_body_707_ = lean_ctor_get(v_e_649_, 3);
v___x_708_ = lean_expr_instantiate1(v_body_707_, v_value_706_);
v___x_709_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_708_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_709_;
goto v___jp_662_;
}
case 3:
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_Expr_isProp(v_e_649_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_Expr_isType(v_e_649_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__4);
v_a_657_ = v___x_712_;
goto v___jp_656_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__6);
v_a_657_ = v___x_713_;
goto v___jp_656_;
}
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___closed__0);
v_a_657_ = v___x_714_;
goto v___jp_656_;
}
}
case 4:
{
lean_object* v_declName_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_declName_715_ = lean_ctor_get(v_e_649_, 0);
v___x_716_ = lean_box(0);
lean_inc(v_declName_715_);
v___x_717_ = l_Lean_Expr_const___override(v_declName_715_, v___x_716_);
v_a_657_ = v___x_717_;
goto v___jp_656_;
}
case 10:
{
lean_object* v_expr_718_; lean_object* v___x_719_; 
v_expr_718_ = lean_ctor_get(v_e_649_, 1);
lean_inc_ref(v_expr_718_);
v___x_719_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_expr_718_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
v___y_663_ = v___x_719_;
goto v___jp_662_;
}
default: 
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_657_ = v___x_720_;
goto v___jp_656_;
}
}
}
else
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__0___closed__0);
v_a_657_ = v___x_721_;
goto v___jp_656_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_e_649_);
v_a_722_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_667_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_667_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_e_649_);
v_val_730_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_666_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_dec(v___x_666_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 0);
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_658_ = lean_st_ref_take(v_a_650_);
lean_inc_ref(v_a_657_);
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v___x_658_, v_e_649_, v_a_657_);
v___x_660_ = lean_st_ref_put(v_a_650_, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v_a_657_);
return v___x_661_;
}
v___jp_662_:
{
if (lean_obj_tag(v___y_663_) == 0)
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___y_663_, 1);
v_a_657_ = v_a_664_;
goto v___jp_656_;
}
else
{
lean_dec_ref(v_e_649_);
return v___y_663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___lam__1(lean_object* v_body_738_, lean_object* v_arg_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_expr_instantiate1(v_body_738_, v_arg_739_);
v___x_747_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v___x_746_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4___boxed(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__4(v_x_748_, v_x_749_, v_x_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___boxed(lean_object* v_upperBound_758_, lean_object* v_args_759_, lean_object* v_a_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_758_, v_args_759_, v_a_760_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v_args_759_);
lean_dec(v_upperBound_758_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0___boxed(lean_object* v_snd_769_, lean_object* v_args_770_, lean_object* v_a_771_, lean_object* v_____r_772_, lean_object* v_fty_773_, lean_object* v_j_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg___lam__0(v_snd_769_, v_args_770_, v_a_771_, v_____r_772_, v_fty_773_, v_j_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v_j_774_);
lean_dec(v_a_771_);
lean_dec_ref(v_args_770_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit___boxed(lean_object* v_e_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(lean_object* v_00_u03b1_790_, lean_object* v_msg_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___boxed(lean_object* v_00_u03b1_798_, lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0(v_00_u03b1_798_, v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(lean_object* v_upperBound_806_, lean_object* v_args_807_, lean_object* v_inst_808_, lean_object* v_R_809_, lean_object* v_a_810_, lean_object* v_b_811_, lean_object* v_c_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___redArg(v_upperBound_806_, v_args_807_, v_a_810_, v_b_811_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1___boxed(lean_object* v_upperBound_820_, lean_object* v_args_821_, lean_object* v_inst_822_, lean_object* v_R_823_, lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v_c_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__1(v_upperBound_820_, v_args_821_, v_inst_822_, v_R_823_, v_a_824_, v_b_825_, v_c_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v_args_821_);
lean_dec(v_upperBound_820_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_m_835_, lean_object* v_a_836_, lean_object* v_b_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2___redArg(v_m_835_, v_a_836_, v_b_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___redArg(v_m_840_, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3___boxed(lean_object* v_00_u03b2_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3(v_00_u03b2_843_, v_m_844_, v_a_845_);
lean_dec_ref(v_a_845_);
lean_dec_ref(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___boxed(lean_object* v_00_u03b2_851_, lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3(v_00_u03b2_851_, v_a_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_a_852_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4(lean_object* v_00_u03b2_856_, lean_object* v_data_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_data_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5(lean_object* v_00_u03b2_859_, lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__5___redArg(v_a_860_, v_b_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___redArg(v_a_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_868_, lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__3_spec__7(v_00_u03b2_868_, v_a_869_, v_x_870_);
lean_dec(v_x_870_);
lean_dec_ref(v_a_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_872_, lean_object* v_i_873_, lean_object* v_source_874_, lean_object* v_target_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6___redArg(v_i_873_, v_source_874_, v_target_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4_spec__6_spec__9___redArg(v_x_878_, v_x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v___x_882_ = lean_unsigned_to_nat(16u);
v___x_883_ = lean_mk_array(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__0);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(lean_object* v_e_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_894_ = lean_st_mk_ref(v___x_893_);
v___x_895_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit(v_e_887_, v___x_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_st_ref_get(v___x_894_);
lean_dec(v___x_894_);
lean_dec(v___x_900_);
if (v_isShared_899_ == 0)
{
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_896_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_dec(v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___boxed(lean_object* v_e_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_e_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(lean_object* v_m_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_buckets_914_; lean_object* v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v_fold_919_; uint64_t v___x_920_; uint64_t v___x_921_; uint64_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_buckets_914_ = lean_ctor_get(v_m_912_, 1);
v___x_915_ = lean_array_get_size(v_buckets_914_);
v___x_916_ = l_Lean_Expr_hash(v_a_913_);
v___x_917_ = 32ULL;
v___x_918_ = lean_uint64_shift_right(v___x_916_, v___x_917_);
v_fold_919_ = lean_uint64_xor(v___x_916_, v___x_918_);
v___x_920_ = 16ULL;
v___x_921_ = lean_uint64_shift_right(v_fold_919_, v___x_920_);
v___x_922_ = lean_uint64_xor(v_fold_919_, v___x_921_);
v___x_923_ = lean_uint64_to_usize(v___x_922_);
v___x_924_ = lean_usize_of_nat(v___x_915_);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_sub(v___x_924_, v___x_925_);
v___x_927_ = lean_usize_land(v___x_923_, v___x_926_);
v___x_928_ = lean_array_uget_borrowed(v_buckets_914_, v___x_927_);
v___x_929_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_913_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg___boxed(lean_object* v_m_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_930_, v_a_931_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_m_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(lean_object* v_m_934_, lean_object* v_a_935_, lean_object* v_b_936_){
_start:
{
lean_object* v_size_937_; lean_object* v_buckets_938_; lean_object* v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v_fold_943_; uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v_bkt_952_; uint8_t v___x_953_; 
v_size_937_ = lean_ctor_get(v_m_934_, 0);
v_buckets_938_ = lean_ctor_get(v_m_934_, 1);
v___x_939_ = lean_array_get_size(v_buckets_938_);
v___x_940_ = l_Lean_Expr_hash(v_a_935_);
v___x_941_ = 32ULL;
v___x_942_ = lean_uint64_shift_right(v___x_940_, v___x_941_);
v_fold_943_ = lean_uint64_xor(v___x_940_, v___x_942_);
v___x_944_ = 16ULL;
v___x_945_ = lean_uint64_shift_right(v_fold_943_, v___x_944_);
v___x_946_ = lean_uint64_xor(v_fold_943_, v___x_945_);
v___x_947_ = lean_uint64_to_usize(v___x_946_);
v___x_948_ = lean_usize_of_nat(v___x_939_);
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_sub(v___x_948_, v___x_949_);
v___x_951_ = lean_usize_land(v___x_947_, v___x_950_);
v_bkt_952_ = lean_array_uget_borrowed(v_buckets_938_, v___x_951_);
v___x_953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__3___redArg(v_a_935_, v_bkt_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_974_; 
lean_inc_ref(v_buckets_938_);
lean_inc(v_size_937_);
v_isSharedCheck_974_ = !lean_is_exclusive(v_m_934_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; lean_object* v_unused_976_; 
v_unused_975_ = lean_ctor_get(v_m_934_, 1);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_m_934_, 0);
lean_dec(v_unused_976_);
v___x_955_ = v_m_934_;
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_m_934_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_size_x27_958_; lean_object* v___x_959_; lean_object* v_buckets_x27_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v_size_x27_958_ = lean_nat_add(v_size_937_, v___x_957_);
lean_dec(v_size_937_);
lean_inc(v_bkt_952_);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v_a_935_);
lean_ctor_set(v___x_959_, 1, v_b_936_);
lean_ctor_set(v___x_959_, 2, v_bkt_952_);
v_buckets_x27_960_ = lean_array_uset(v_buckets_938_, v___x_951_, v___x_959_);
v___x_961_ = lean_unsigned_to_nat(4u);
v___x_962_ = lean_nat_mul(v_size_x27_958_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_nat_div(v___x_962_, v___x_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_array_get_size(v_buckets_x27_960_);
v___x_966_ = lean_nat_dec_le(v___x_964_, v___x_965_);
lean_dec(v___x_964_);
if (v___x_966_ == 0)
{
lean_object* v_val_967_; lean_object* v___x_969_; 
v_val_967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__2_spec__4___redArg(v_buckets_x27_960_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_val_967_);
lean_ctor_set(v___x_955_, 0, v_size_x27_958_);
v___x_969_ = v___x_955_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_size_x27_958_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_val_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v___x_972_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_buckets_x27_960_);
lean_ctor_set(v___x_955_, 0, v_size_x27_958_);
v___x_972_ = v___x_955_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_size_x27_958_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_buckets_x27_960_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_dec(v_b_936_);
lean_dec_ref(v_a_935_);
return v_m_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(lean_object* v_e_982_, uint8_t v_omitTopForall_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
switch(lean_obj_tag(v_e_982_))
{
case 4:
{
lean_object* v_declName_990_; lean_object* v___x_991_; lean_object* v_seen_992_; lean_object* v_consts_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1020_; 
v_declName_990_ = lean_ctor_get(v_e_982_, 0);
lean_inc(v_declName_990_);
lean_dec_ref_known(v_e_982_, 2);
v___x_991_ = lean_st_ref_take(v_a_984_);
v_seen_992_ = lean_ctor_get(v___x_991_, 0);
v_consts_993_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_995_ = v___x_991_;
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_consts_993_);
lean_inc(v_seen_992_);
lean_dec(v___x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc(v_declName_990_);
v___x_997_ = l_Lean_NameSet_insert(v_consts_993_, v_declName_990_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_seen_992_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1019_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_st_ref_put(v_a_984_, v___x_999_);
v___x_1001_ = l_Lean_Name_eraseMacroScopes(v_declName_990_);
lean_dec(v_declName_990_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_str_1002_; lean_object* v___x_1003_; uint32_t v___x_1004_; uint8_t v___y_1006_; uint32_t v___x_1013_; uint8_t v___x_1014_; 
v_str_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc_ref(v_str_1002_);
lean_dec_ref_known(v___x_1001_, 2);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_string_utf8_get(v_str_1002_, v___x_1003_);
v___x_1013_ = 97;
v___x_1014_ = lean_uint32_dec_le(v___x_1013_, v___x_1004_);
if (v___x_1014_ == 0)
{
v___y_1006_ = v___x_1014_;
goto v___jp_1005_;
}
else
{
uint32_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = 122;
v___x_1016_ = lean_uint32_dec_le(v___x_1004_, v___x_1015_);
v___y_1006_ = v___x_1016_;
goto v___jp_1005_;
}
v___jp_1005_:
{
if (v___y_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_string_utf8_set(v_str_1002_, v___x_1003_, v___x_1004_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
else
{
uint32_t v___x_1009_; uint32_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1009_ = 4294967264;
v___x_1010_ = lean_uint32_add(v___x_1004_, v___x_1009_);
v___x_1011_ = lean_string_utf8_set(v_str_1002_, v___x_1003_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v___x_1001_);
v___x_1017_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
}
}
case 5:
{
lean_object* v_fn_1021_; lean_object* v_arg_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_fn_1021_ = lean_ctor_get(v_e_982_, 0);
lean_inc_ref(v_fn_1021_);
v_arg_1022_ = lean_ctor_get(v_e_982_, 1);
lean_inc_ref(v_arg_1022_);
lean_dec_ref_known(v_e_982_, 2);
v___x_1023_ = 0;
v___x_1024_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_fn_1021_, v___x_1023_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_arg_1022_, v___x_1023_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_string_append(v_a_1025_, v_a_1027_);
lean_dec(v_a_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
case 7:
{
lean_object* v_binderType_1036_; lean_object* v_body_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; 
v_binderType_1036_ = lean_ctor_get(v_e_982_, 1);
lean_inc_ref(v_binderType_1036_);
v_body_1037_ = lean_ctor_get(v_e_982_, 2);
lean_inc_ref(v_body_1037_);
lean_dec_ref_known(v_e_982_, 3);
v___x_1038_ = 0;
v___x_1039_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1036_, v___x_1038_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
if (v_omitTopForall_983_ == 0)
{
goto v___jp_1041_;
}
else
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1055_ = lean_string_dec_eq(v_a_1040_, v___x_1054_);
if (v___x_1055_ == 0)
{
goto v___jp_1041_;
}
else
{
lean_object* v___x_1056_; 
lean_dec(v_a_1040_);
v___x_1056_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1037_, v_omitTopForall_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1056_;
}
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1053_; 
v___x_1042_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_body_1037_, v___x_1038_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__0));
v___x_1048_ = lean_string_append(v___x_1047_, v_a_1040_);
lean_dec(v_a_1040_);
v___x_1049_ = lean_string_append(v___x_1048_, v_a_1043_);
lean_dec(v_a_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
case 3:
{
lean_object* v_u_1057_; 
v_u_1057_ = lean_ctor_get(v_e_982_, 0);
lean_inc(v_u_1057_);
lean_dec_ref_known(v_e_982_, 1);
switch(lean_obj_tag(v_u_1057_))
{
case 0:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__1));
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
case 1:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref_known(v_u_1057_, 1);
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__2));
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
default: 
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec(v_u_1057_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___closed__3));
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
default: 
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v_e_982_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(lean_object* v_e_1066_, uint8_t v_omitTopForall_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_seen_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_st_ref_get(v_a_1068_);
v_seen_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_seen_1075_);
lean_dec(v___x_1074_);
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_seen_1075_, v_e_1066_);
lean_dec_ref(v_seen_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1098_; 
lean_inc_ref(v_e_1066_);
v___x_1077_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1066_, v_omitTopForall_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1098_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1098_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_seen_1083_; lean_object* v_consts_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1097_; 
v___x_1082_ = lean_st_ref_take(v_a_1068_);
v_seen_1083_ = lean_ctor_get(v___x_1082_, 0);
v_consts_1084_ = lean_ctor_get(v___x_1082_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1086_ = v___x_1082_;
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_consts_1084_);
lean_inc(v_seen_1083_);
lean_dec(v___x_1082_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1083_, v_e_1066_, v___x_1088_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_consts_1084_);
v___x_1091_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_st_ref_put(v_a_1068_, v___x_1091_);
if (v_isShared_1081_ == 0)
{
v___x_1094_ = v___x_1080_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1078_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v_e_1066_);
v___x_1099_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___boxed(lean_object* v_e_1101_, lean_object* v_omitTopForall_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
uint8_t v_omitTopForall_boxed_1109_; lean_object* v_res_1110_; 
v_omitTopForall_boxed_1109_ = lean_unbox(v_omitTopForall_1102_);
v_res_1110_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1101_, v_omitTopForall_boxed_1109_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27___boxed(lean_object* v_e_1111_, lean_object* v_omitTopForall_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
uint8_t v_omitTopForall_boxed_1119_; lean_object* v_res_1120_; 
v_omitTopForall_boxed_1119_ = lean_unbox(v_omitTopForall_1112_);
v_res_1120_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27(v_e_1111_, v_omitTopForall_boxed_1119_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___redArg(v_m_1122_, v_a_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_m_1126_, lean_object* v_a_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__0(v_00_u03b2_1125_, v_m_1126_, v_a_1127_);
lean_dec_ref(v_a_1127_);
lean_dec_ref(v_m_1126_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1(lean_object* v_00_u03b2_1130_, lean_object* v_m_1131_, lean_object* v_a_1132_, lean_object* v_b_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_m_1131_, v_a_1132_, v_b_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter___redArg(lean_object* v_e_1135_, lean_object* v_h__1_1136_, lean_object* v_h__2_1137_, lean_object* v_h__3_1138_, lean_object* v_h__4_1139_, lean_object* v_h__5_1140_, lean_object* v_h__6_1141_, lean_object* v_h__7_1142_){
_start:
{
switch(lean_obj_tag(v_e_1135_))
{
case 4:
{
lean_object* v_declName_1143_; lean_object* v_us_1144_; lean_object* v___x_1145_; 
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
v_declName_1143_ = lean_ctor_get(v_e_1135_, 0);
lean_inc(v_declName_1143_);
v_us_1144_ = lean_ctor_get(v_e_1135_, 1);
lean_inc(v_us_1144_);
lean_dec_ref_known(v_e_1135_, 2);
v___x_1145_ = lean_apply_2(v_h__1_1136_, v_declName_1143_, v_us_1144_);
return v___x_1145_;
}
case 5:
{
lean_object* v_fn_1146_; lean_object* v_arg_1147_; lean_object* v___x_1148_; 
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__1_1136_);
v_fn_1146_ = lean_ctor_get(v_e_1135_, 0);
lean_inc_ref(v_fn_1146_);
v_arg_1147_ = lean_ctor_get(v_e_1135_, 1);
lean_inc_ref(v_arg_1147_);
lean_dec_ref_known(v_e_1135_, 2);
v___x_1148_ = lean_apply_2(v_h__2_1137_, v_fn_1146_, v_arg_1147_);
return v___x_1148_;
}
case 7:
{
lean_object* v_binderName_1149_; lean_object* v_binderType_1150_; lean_object* v_body_1151_; uint8_t v_binderInfo_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_binderName_1149_ = lean_ctor_get(v_e_1135_, 0);
lean_inc(v_binderName_1149_);
v_binderType_1150_ = lean_ctor_get(v_e_1135_, 1);
lean_inc_ref(v_binderType_1150_);
v_body_1151_ = lean_ctor_get(v_e_1135_, 2);
lean_inc_ref(v_body_1151_);
v_binderInfo_1152_ = lean_ctor_get_uint8(v_e_1135_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1135_, 3);
v___x_1153_ = lean_box(v_binderInfo_1152_);
v___x_1154_ = lean_apply_4(v_h__3_1138_, v_binderName_1149_, v_binderType_1150_, v_body_1151_, v___x_1153_);
return v___x_1154_;
}
case 3:
{
lean_object* v_u_1155_; 
lean_dec(v_h__7_1142_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_u_1155_ = lean_ctor_get(v_e_1135_, 0);
lean_inc(v_u_1155_);
lean_dec_ref_known(v_e_1135_, 1);
switch(lean_obj_tag(v_u_1155_))
{
case 0:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_apply_1(v_h__4_1139_, v___x_1156_);
return v___x_1157_;
}
case 1:
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__6_1141_);
lean_dec(v_h__4_1139_);
v_a_1158_ = lean_ctor_get(v_u_1155_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v_u_1155_, 1);
v___x_1159_ = lean_apply_1(v_h__5_1140_, v_a_1158_);
return v___x_1159_;
}
default: 
{
lean_object* v___x_1160_; 
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
v___x_1160_ = lean_apply_3(v_h__6_1141_, v_u_1155_, lean_box(0), lean_box(0));
return v___x_1160_;
}
}
}
default: 
{
lean_object* v___x_1161_; 
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v___x_1161_ = lean_apply_7(v_h__7_1142_, v_e_1135_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__3_splitter(lean_object* v_motive_1162_, lean_object* v_e_1163_, lean_object* v_h__1_1164_, lean_object* v_h__2_1165_, lean_object* v_h__3_1166_, lean_object* v_h__4_1167_, lean_object* v_h__5_1168_, lean_object* v_h__6_1169_, lean_object* v_h__7_1170_){
_start:
{
switch(lean_obj_tag(v_e_1163_))
{
case 4:
{
lean_object* v_declName_1171_; lean_object* v_us_1172_; lean_object* v___x_1173_; 
lean_dec(v_h__7_1170_);
lean_dec(v_h__6_1169_);
lean_dec(v_h__5_1168_);
lean_dec(v_h__4_1167_);
lean_dec(v_h__3_1166_);
lean_dec(v_h__2_1165_);
v_declName_1171_ = lean_ctor_get(v_e_1163_, 0);
lean_inc(v_declName_1171_);
v_us_1172_ = lean_ctor_get(v_e_1163_, 1);
lean_inc(v_us_1172_);
lean_dec_ref_known(v_e_1163_, 2);
v___x_1173_ = lean_apply_2(v_h__1_1164_, v_declName_1171_, v_us_1172_);
return v___x_1173_;
}
case 5:
{
lean_object* v_fn_1174_; lean_object* v_arg_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__7_1170_);
lean_dec(v_h__6_1169_);
lean_dec(v_h__5_1168_);
lean_dec(v_h__4_1167_);
lean_dec(v_h__3_1166_);
lean_dec(v_h__1_1164_);
v_fn_1174_ = lean_ctor_get(v_e_1163_, 0);
lean_inc_ref(v_fn_1174_);
v_arg_1175_ = lean_ctor_get(v_e_1163_, 1);
lean_inc_ref(v_arg_1175_);
lean_dec_ref_known(v_e_1163_, 2);
v___x_1176_ = lean_apply_2(v_h__2_1165_, v_fn_1174_, v_arg_1175_);
return v___x_1176_;
}
case 7:
{
lean_object* v_binderName_1177_; lean_object* v_binderType_1178_; lean_object* v_body_1179_; uint8_t v_binderInfo_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_h__7_1170_);
lean_dec(v_h__6_1169_);
lean_dec(v_h__5_1168_);
lean_dec(v_h__4_1167_);
lean_dec(v_h__2_1165_);
lean_dec(v_h__1_1164_);
v_binderName_1177_ = lean_ctor_get(v_e_1163_, 0);
lean_inc(v_binderName_1177_);
v_binderType_1178_ = lean_ctor_get(v_e_1163_, 1);
lean_inc_ref(v_binderType_1178_);
v_body_1179_ = lean_ctor_get(v_e_1163_, 2);
lean_inc_ref(v_body_1179_);
v_binderInfo_1180_ = lean_ctor_get_uint8(v_e_1163_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1163_, 3);
v___x_1181_ = lean_box(v_binderInfo_1180_);
v___x_1182_ = lean_apply_4(v_h__3_1166_, v_binderName_1177_, v_binderType_1178_, v_body_1179_, v___x_1181_);
return v___x_1182_;
}
case 3:
{
lean_object* v_u_1183_; 
lean_dec(v_h__7_1170_);
lean_dec(v_h__3_1166_);
lean_dec(v_h__2_1165_);
lean_dec(v_h__1_1164_);
v_u_1183_ = lean_ctor_get(v_e_1163_, 0);
lean_inc(v_u_1183_);
lean_dec_ref_known(v_e_1163_, 1);
switch(lean_obj_tag(v_u_1183_))
{
case 0:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_h__6_1169_);
lean_dec(v_h__5_1168_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_apply_1(v_h__4_1167_, v___x_1184_);
return v___x_1185_;
}
case 1:
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
lean_dec(v_h__6_1169_);
lean_dec(v_h__4_1167_);
v_a_1186_ = lean_ctor_get(v_u_1183_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v_u_1183_, 1);
v___x_1187_ = lean_apply_1(v_h__5_1168_, v_a_1186_);
return v___x_1187_;
}
default: 
{
lean_object* v___x_1188_; 
lean_dec(v_h__5_1168_);
lean_dec(v_h__4_1167_);
v___x_1188_ = lean_apply_3(v_h__6_1169_, v_u_1183_, lean_box(0), lean_box(0));
return v___x_1188_;
}
}
}
default: 
{
lean_object* v___x_1189_; 
lean_dec(v_h__6_1169_);
lean_dec(v_h__5_1168_);
lean_dec(v_h__4_1167_);
lean_dec(v_h__3_1166_);
lean_dec(v_h__2_1165_);
lean_dec(v_h__1_1164_);
v___x_1189_ = lean_apply_7(v_h__7_1170_, v_e_1163_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter___redArg(lean_object* v_x_1190_, lean_object* v_h__1_1191_, lean_object* v_h__2_1192_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 1)
{
lean_object* v_pre_1193_; lean_object* v_str_1194_; lean_object* v___x_1195_; 
lean_dec(v_h__2_1192_);
v_pre_1193_ = lean_ctor_get(v_x_1190_, 0);
lean_inc(v_pre_1193_);
v_str_1194_ = lean_ctor_get(v_x_1190_, 1);
lean_inc_ref(v_str_1194_);
lean_dec_ref_known(v_x_1190_, 2);
v___x_1195_ = lean_apply_2(v_h__1_1191_, v_pre_1193_, v_str_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
lean_dec(v_h__1_1191_);
v___x_1196_ = lean_apply_2(v_h__2_1192_, v_x_1190_, lean_box(0));
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_x27_match__1_splitter(lean_object* v_motive_1197_, lean_object* v_x_1198_, lean_object* v_h__1_1199_, lean_object* v_h__2_1200_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 1)
{
lean_object* v_pre_1201_; lean_object* v_str_1202_; lean_object* v___x_1203_; 
lean_dec(v_h__2_1200_);
v_pre_1201_ = lean_ctor_get(v_x_1198_, 0);
lean_inc(v_pre_1201_);
v_str_1202_ = lean_ctor_get(v_x_1198_, 1);
lean_inc_ref(v_str_1202_);
lean_dec_ref_known(v_x_1198_, 2);
v___x_1203_ = lean_apply_2(v_h__1_1199_, v_pre_1201_, v_str_1202_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_h__1_1199_);
v___x_1204_ = lean_apply_2(v_h__2_1200_, v_x_1198_, lean_box(0));
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(lean_object* v_e_1205_, uint8_t v_omitTopForall_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1205_, v_omitTopForall_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore___boxed(lean_object* v_e_1214_, lean_object* v_omitTopForall_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
uint8_t v_omitTopForall_boxed_1222_; lean_object* v_res_1223_; 
v_omitTopForall_boxed_1222_ = lean_unbox(v_omitTopForall_1215_);
v_res_1223_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore(v_e_1214_, v_omitTopForall_boxed_1222_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(lean_object* v_e_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
if (lean_obj_tag(v_e_1225_) == 7)
{
lean_object* v_binderType_1232_; lean_object* v_body_1233_; lean_object* v___x_1234_; 
v_binderType_1232_ = lean_ctor_get(v_e_1225_, 1);
lean_inc_ref(v_binderType_1232_);
v_body_1233_ = lean_ctor_get(v_e_1225_, 2);
lean_inc_ref(v_body_1233_);
lean_dec_ref_known(v_e_1225_, 3);
v___x_1234_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_body_1233_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_fst_1236_ = lean_ctor_get(v_a_1235_, 0);
v_snd_1237_ = lean_ctor_get(v_a_1235_, 1);
v___x_1238_ = 1;
v___x_1239_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_binderType_1232_, v___x_1238_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1264_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1245_ = lean_string_dec_eq(v_a_1240_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1258_; 
lean_inc(v_snd_1237_);
lean_inc(v_fst_1236_);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_a_1235_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v_a_1235_, 1);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_a_1235_, 0);
lean_dec(v_unused_1260_);
v___x_1247_ = v_a_1235_;
v_isShared_1248_ = v_isSharedCheck_1258_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v_a_1235_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1258_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___closed__0));
v___x_1250_ = lean_string_append(v___x_1249_, v_a_1240_);
lean_dec(v_a_1240_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_fst_1236_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1251_);
v___x_1253_ = v___x_1247_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_snd_1237_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1253_);
v___x_1255_ = v___x_1242_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v_a_1240_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_a_1235_);
v___x_1262_ = v___x_1242_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1235_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1235_);
v_a_1265_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1239_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1239_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
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
else
{
lean_dec_ref(v_binderType_1232_);
return v___x_1234_;
}
}
else
{
uint8_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = 0;
v___x_1274_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit(v_e_1225_, v___x_1273_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1274_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1274_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit___boxed(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
return v_x_1301_;
}
else
{
lean_object* v_head_1303_; lean_object* v_tail_1304_; lean_object* v___x_1305_; 
v_head_1303_ = lean_ctor_get(v_x_1302_, 0);
v_tail_1304_ = lean_ctor_get(v_x_1302_, 1);
v___x_1305_ = lean_string_append(v_x_1301_, v_head_1303_);
v_x_1301_ = v___x_1305_;
v_x_1302_ = v_tail_1304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0___boxed(lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v_x_1307_, v_x_1308_);
lean_dec(v_x_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(lean_object* v_e_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_visit(v_e_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1330_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v_fst_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_fst_1322_);
v_snd_1323_ = lean_ctor_get(v_a_1318_, 1);
lean_inc(v_snd_1323_);
lean_dec(v_a_1318_);
v___x_1324_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_1325_ = l_List_foldl___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux_spec__0(v___x_1324_, v_fst_1322_);
lean_dec(v_fst_1322_);
v___x_1326_ = lean_string_append(v_snd_1323_, v___x_1325_);
lean_dec_ref(v___x_1325_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1326_);
v___x_1328_ = v___x_1320_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_a_1331_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1317_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1317_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux___boxed(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_e_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(lean_object* v_ns_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
switch(lean_obj_tag(v_ns_1347_))
{
case 0:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
case 1:
{
lean_object* v_pre_1353_; lean_object* v___x_1354_; lean_object* v_env_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; 
v_pre_1353_ = lean_ctor_get(v_ns_1347_, 0);
lean_inc(v_pre_1353_);
v___x_1354_ = lean_st_ref_get(v_a_1349_);
v_env_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_ref(v_env_1355_);
lean_dec(v___x_1354_);
v___x_1356_ = 1;
lean_inc_ref(v_ns_1347_);
v___x_1357_ = l_Lean_Environment_contains(v_env_1355_, v_ns_1347_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec_ref_known(v_ns_1347_, 2);
v_ns_1347_ = v_pre_1353_;
goto _start;
}
else
{
lean_object* v___x_1359_; lean_object* v_seen_1360_; lean_object* v_consts_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v___x_1359_ = lean_st_ref_take(v_a_1348_);
v_seen_1360_ = lean_ctor_get(v___x_1359_, 0);
v_consts_1361_ = lean_ctor_get(v___x_1359_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1363_ = v___x_1359_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_consts_1361_);
lean_inc(v_seen_1360_);
lean_dec(v___x_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1365_ = lean_box(0);
lean_inc_ref(v_ns_1347_);
v___x_1366_ = l_Lean_Expr_const___override(v_ns_1347_, v___x_1365_);
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit_spec__1___redArg(v_seen_1360_, v___x_1366_, v___x_1367_);
v___x_1369_ = l_Lean_NameSet_insert(v_consts_1361_, v_ns_1347_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1369_);
lean_ctor_set(v___x_1363_, 0, v___x_1368_);
v___x_1371_ = v___x_1363_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_st_ref_put(v_a_1348_, v___x_1371_);
v_ns_1347_ = v_pre_1353_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_pre_1376_; 
v_pre_1376_ = lean_ctor_get(v_ns_1347_, 0);
lean_inc(v_pre_1376_);
lean_dec_ref_known(v_ns_1347_, 2);
v_ns_1347_ = v_pre_1376_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg___boxed(lean_object* v_ns_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec(v_a_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(lean_object* v_ns_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_ns_1383_, v_a_1384_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___boxed(lean_object* v_ns_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace(v_ns_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(lean_object* v_e_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Lean_Expr_hasMVar(v_e_1399_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_e_1399_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v___x_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1409_; lean_object* v_cache_1410_; lean_object* v_zetaDeltaFVarIds_1411_; lean_object* v_postponed_1412_; lean_object* v_diag_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1422_; 
v___x_1404_ = lean_st_ref_get(v___y_1400_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = l_Lean_instantiateMVarsCore(v_mctx_1405_, v_e_1399_);
v_fst_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v___x_1406_, 1);
lean_inc(v_snd_1408_);
lean_dec_ref(v___x_1406_);
v___x_1409_ = lean_st_ref_take(v___y_1400_);
v_cache_1410_ = lean_ctor_get(v___x_1409_, 1);
v_zetaDeltaFVarIds_1411_ = lean_ctor_get(v___x_1409_, 2);
v_postponed_1412_ = lean_ctor_get(v___x_1409_, 3);
v_diag_1413_ = lean_ctor_get(v___x_1409_, 4);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1423_);
v___x_1415_ = v___x_1409_;
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_diag_1413_);
lean_inc(v_postponed_1412_);
lean_inc(v_zetaDeltaFVarIds_1411_);
lean_inc(v_cache_1410_);
lean_dec(v___x_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v_snd_1408_);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_snd_1408_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_cache_1410_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_zetaDeltaFVarIds_1411_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_postponed_1412_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_diag_1413_);
v___x_1418_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_st_ref_put(v___y_1400_, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_fst_1407_);
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg___boxed(lean_object* v_e_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1424_, v___y_1425_);
lean_dec(v___y_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(lean_object* v_e_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1428_, v___y_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___boxed(lean_object* v_e_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0(v_e_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(lean_object* v_e_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v_toCold_1452_; lean_object* v_a_1453_; lean_object* v_currNamespace_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1451_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName_spec__0___redArg(v_e_1444_, v_a_1447_);
v_toCold_1452_ = lean_ctor_get(v_a_1448_, 0);
v_a_1453_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1451_);
v_currNamespace_1454_ = lean_ctor_get(v_toCold_1452_, 4);
lean_inc(v_currNamespace_1454_);
v___x_1455_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_visitNamespace___redArg(v_currNamespace_1454_, v_a_1445_, v_a_1449_);
lean_dec_ref(v___x_1455_);
v___x_1456_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr(v_a_1453_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameAux(v_a_1457_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
return v___x_1458_;
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1456_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1456_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName___boxed(lean_object* v_e_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_e_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(lean_object* v_x_1476_){
_start:
{
switch(lean_obj_tag(v_x_1476_))
{
case 0:
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
return v___x_1477_;
}
case 1:
{
lean_object* v_pre_1478_; lean_object* v_str_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint32_t v___x_1484_; uint8_t v___y_1486_; uint32_t v___x_1493_; uint8_t v___x_1494_; 
v_pre_1478_ = lean_ctor_get(v_x_1476_, 0);
lean_inc(v_pre_1478_);
v_str_1479_ = lean_ctor_get(v_x_1476_, 1);
lean_inc_ref(v_str_1479_);
lean_dec_ref_known(v_x_1476_, 2);
v___x_1480_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v_pre_1478_);
v___x_1481_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix___closed__0));
v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_string_utf8_get(v_str_1479_, v___x_1483_);
v___x_1493_ = 65;
v___x_1494_ = lean_uint32_dec_le(v___x_1493_, v___x_1484_);
if (v___x_1494_ == 0)
{
v___y_1486_ = v___x_1494_;
goto v___jp_1485_;
}
else
{
uint32_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = 90;
v___x_1496_ = lean_uint32_dec_le(v___x_1484_, v___x_1495_);
v___y_1486_ = v___x_1496_;
goto v___jp_1485_;
}
v___jp_1485_:
{
if (v___y_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_string_utf8_set(v_str_1479_, v___x_1483_, v___x_1484_);
v___x_1488_ = lean_string_append(v___x_1482_, v___x_1487_);
lean_dec_ref(v___x_1487_);
return v___x_1488_;
}
else
{
uint32_t v___x_1489_; uint32_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = 32;
v___x_1490_ = lean_uint32_add(v___x_1484_, v___x_1489_);
v___x_1491_ = lean_string_utf8_set(v_str_1479_, v___x_1483_, v___x_1490_);
v___x_1492_ = lean_string_append(v___x_1482_, v___x_1491_);
lean_dec_ref(v___x_1491_);
return v___x_1492_;
}
}
}
default: 
{
lean_object* v_pre_1497_; 
v_pre_1497_ = lean_ctor_get(v_x_1476_, 0);
lean_inc(v_pre_1497_);
lean_dec_ref_known(v_x_1476_, 2);
v_x_1476_ = v_pre_1497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v_env_1502_; lean_object* v___x_1503_; lean_object* v_mainModule_1504_; lean_object* v___x_1505_; 
v___x_1501_ = lean_st_ref_get(v___y_1499_);
v_env_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_env_1502_);
lean_dec(v___x_1501_);
v___x_1503_ = l_Lean_Environment_header(v_env_1502_);
lean_dec_ref(v_env_1502_);
v_mainModule_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_mainModule_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_mainModule_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg___boxed(lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1506_);
lean_dec(v___y_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___boxed(lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1(v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
if (lean_obj_tag(v_x_1522_) == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = 1;
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = 0;
return v___x_1524_;
}
}
else
{
if (lean_obj_tag(v_x_1522_) == 0)
{
uint8_t v___x_1525_; 
v___x_1525_ = 0;
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; lean_object* v_val_1527_; uint8_t v___x_1528_; 
v_val_1526_ = lean_ctor_get(v_x_1521_, 0);
v_val_1527_ = lean_ctor_get(v_x_1522_, 0);
v___x_1528_ = lean_name_eq(v_val_1526_, v_val_1527_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2___boxed(lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v_x_1529_, v_x_1530_);
lean_dec(v_x_1530_);
lean_dec(v_x_1529_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(lean_object* v_e_1533_){
_start:
{
if (lean_obj_tag(v_e_1533_) == 4)
{
lean_object* v_declName_1534_; uint8_t v___x_1535_; 
v_declName_1534_ = lean_ctor_get(v_e_1533_, 0);
v___x_1535_ = l_Lean_Name_hasMacroScopes(v_declName_1534_);
return v___x_1535_;
}
else
{
uint8_t v___x_1536_; 
v___x_1536_ = 0;
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0___boxed(lean_object* v_e_1537_){
_start:
{
uint8_t v_res_1538_; lean_object* v_r_1539_; 
v_res_1538_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___lam__0(v_e_1537_);
lean_dec_ref(v_e_1537_);
v_r_1539_ = lean_box(v_res_1538_);
return v_r_1539_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(lean_object* v_as_1540_, size_t v_i_1541_, size_t v_stop_1542_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_eq(v_i_1541_, v_stop_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_array_uget_borrowed(v_as_1540_, v_i_1541_);
if (lean_obj_tag(v___x_1544_) == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = 1;
return v___x_1545_;
}
else
{
size_t v___x_1546_; size_t v___x_1547_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1541_, v___x_1546_);
v_i_1541_ = v___x_1547_;
goto _start;
}
}
else
{
uint8_t v___x_1549_; 
v___x_1549_ = 0;
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5___boxed(lean_object* v_as_1550_, lean_object* v_i_1551_, lean_object* v_stop_1552_){
_start:
{
size_t v_i_boxed_1553_; size_t v_stop_boxed_1554_; uint8_t v_res_1555_; lean_object* v_r_1556_; 
v_i_boxed_1553_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_stop_boxed_1554_ = lean_unbox_usize(v_stop_1552_);
lean_dec(v_stop_1552_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_as_1550_, v_i_boxed_1553_, v_stop_boxed_1554_);
lean_dec_ref(v_as_1550_);
v_r_1556_ = lean_box(v_res_1555_);
return v_r_1556_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(lean_object* v___x_1557_, lean_object* v_as_1558_, size_t v_i_1559_, size_t v_stop_1560_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_eq(v_i_1559_, v_stop_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; lean_object* v___y_1564_; lean_object* v___x_1570_; 
v___x_1562_ = 1;
v___x_1570_ = lean_array_uget(v_as_1558_, v_i_1559_);
if (lean_obj_tag(v___x_1570_) == 0)
{
v___y_1564_ = v___x_1570_;
goto v___jp_1563_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1579_; 
v_val_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_val_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = l_Lean_Name_getRoot(v_val_1571_);
lean_dec(v_val_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v___y_1564_ = v___x_1577_;
goto v___jp_1563_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
lean_inc(v___x_1557_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1557_);
v___x_1566_ = l_Option_instBEq_beq___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__2(v___y_1564_, v___x_1565_);
lean_dec_ref_known(v___x_1565_, 1);
lean_dec(v___y_1564_);
if (v___x_1566_ == 0)
{
size_t v___x_1567_; size_t v___x_1568_; 
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1559_, v___x_1567_);
v_i_1559_ = v___x_1568_;
goto _start;
}
else
{
lean_dec(v___x_1557_);
return v___x_1562_;
}
}
}
else
{
uint8_t v___x_1580_; 
lean_dec(v___x_1557_);
v___x_1580_ = 0;
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4___boxed(lean_object* v___x_1581_, lean_object* v_as_1582_, lean_object* v_i_1583_, lean_object* v_stop_1584_){
_start:
{
size_t v_i_boxed_1585_; size_t v_stop_boxed_1586_; uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_i_boxed_1585_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_stop_boxed_1586_ = lean_unbox_usize(v_stop_1584_);
lean_dec(v_stop_1584_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1581_, v_as_1582_, v_i_boxed_1585_, v_stop_boxed_1586_);
lean_dec_ref(v_as_1582_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
lean_ctor_set(v___x_1594_, 3, v___x_1593_);
lean_ctor_set(v___x_1594_, 4, v___x_1592_);
lean_ctor_set(v___x_1594_, 5, v___x_1592_);
lean_ctor_set(v___x_1594_, 6, v___x_1592_);
lean_ctor_set(v___x_1594_, 7, v___x_1592_);
lean_ctor_set(v___x_1594_, 8, v___x_1592_);
lean_ctor_set(v___x_1594_, 9, v___x_1592_);
lean_ctor_set(v___x_1594_, 10, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_unsigned_to_nat(32u);
v___x_1596_ = lean_mk_empty_array_with_capacity(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1598_ = ((size_t)5ULL);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_unsigned_to_nat(32u);
v___x_1601_ = lean_mk_empty_array_with_capacity(v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_1603_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1601_);
lean_ctor_set(v___x_1603_, 2, v___x_1599_);
lean_ctor_set(v___x_1603_, 3, v___x_1599_);
lean_ctor_set_usize(v___x_1603_, 4, v___x_1598_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1604_ = lean_box(1);
v___x_1605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_1606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_1607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___x_1605_);
lean_ctor_set(v___x_1607_, 2, v___x_1604_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_1622_ = l_Lean_stringToMessageData(v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_1625_ = l_Lean_stringToMessageData(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_1628_ = l_Lean_stringToMessageData(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_1629_, lean_object* v_declHint_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_env_1635_; uint8_t v___x_1636_; 
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_st_ref_get(v___y_1631_);
v_env_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc_ref(v_env_1635_);
lean_dec(v___x_1634_);
v___x_1636_ = l_Lean_Name_isAnonymous(v_declHint_1630_);
if (v___x_1636_ == 0)
{
uint8_t v_isExporting_1637_; 
v_isExporting_1637_ = lean_ctor_get_uint8(v_env_1635_, sizeof(void*)*8);
if (v_isExporting_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref(v_env_1635_);
lean_dec(v_declHint_1630_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_msg_1629_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
lean_inc_ref(v_env_1635_);
v___x_1639_ = l_Lean_Environment_setExporting(v_env_1635_, v___x_1636_);
lean_inc(v_declHint_1630_);
lean_inc_ref(v___x_1639_);
v___x_1640_ = l_Lean_Environment_contains(v___x_1639_, v_declHint_1630_, v_isExporting_1637_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v___x_1639_);
lean_dec_ref(v_env_1635_);
lean_dec(v_declHint_1630_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_msg_1629_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v_c_1647_; lean_object* v___x_1648_; 
v___x_1642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_1643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_1644_ = l_Lean_Options_empty;
v___x_1645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1639_);
lean_ctor_set(v___x_1645_, 1, v___x_1642_);
lean_ctor_set(v___x_1645_, 2, v___x_1643_);
lean_ctor_set(v___x_1645_, 3, v___x_1644_);
lean_inc(v_declHint_1630_);
v___x_1646_ = l_Lean_MessageData_ofConstName(v_declHint_1630_, v___x_1636_);
v_c_1647_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1647_, 0, v___x_1645_);
lean_ctor_set(v_c_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1635_, v_declHint_1630_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v_env_1635_);
lean_dec(v_declHint_1630_);
v___x_1649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_c_1647_);
v___x_1651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_MessageData_note(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_msg_1629_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1690_; 
v_val_1656_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1658_ = v___x_1648_;
v_isShared_1659_ = v_isSharedCheck_1690_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_val_1656_);
lean_dec(v___x_1648_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1690_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_mod_1662_; uint8_t v___x_1663_; 
v___x_1660_ = l_Lean_Environment_header(v_env_1635_);
lean_dec_ref(v_env_1635_);
v___x_1661_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1660_);
v_mod_1662_ = lean_array_get(v___x_1633_, v___x_1661_, v_val_1656_);
lean_dec(v_val_1656_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = l_Lean_isPrivateName(v_declHint_1630_);
lean_dec(v_declHint_1630_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_c_1647_);
v___x_1666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_MessageData_ofName(v_mod_1662_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_MessageData_note(v___x_1671_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_msg_1629_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1673_);
v___x_1675_ = v___x_1658_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_c_1647_);
v___x_1679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_MessageData_ofName(v_mod_1662_);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_MessageData_note(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_msg_1629_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1686_);
v___x_1688_ = v___x_1658_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
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
}
}
else
{
lean_object* v___x_1691_; 
lean_dec_ref(v_env_1635_);
lean_dec(v_declHint_1630_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_msg_1629_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_1692_, lean_object* v_declHint_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1692_, v_declHint_1693_, v___y_1694_);
lean_dec(v___y_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(lean_object* v_msg_1697_, lean_object* v_declHint_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1714_; 
v___x_1704_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_1697_, v_declHint_1698_, v___y_1702_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1709_ = l_Lean_unknownIdentifierMessageTag;
v___x_1710_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v_a_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1710_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1715_, lean_object* v_declHint_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1715_, v_declHint_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_toCold_1730_; lean_object* v_currRecDepth_1731_; lean_object* v_ref_1732_; uint8_t v_diag_1733_; uint8_t v_suppressElabErrors_1734_; lean_object* v_ref_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_toCold_1730_ = lean_ctor_get(v___y_1727_, 0);
v_currRecDepth_1731_ = lean_ctor_get(v___y_1727_, 1);
v_ref_1732_ = lean_ctor_get(v___y_1727_, 2);
v_diag_1733_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*3);
v_suppressElabErrors_1734_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*3 + 1);
v_ref_1735_ = l_Lean_replaceRef(v_ref_1723_, v_ref_1732_);
lean_inc(v_currRecDepth_1731_);
lean_inc_ref(v_toCold_1730_);
v___x_1736_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1736_, 0, v_toCold_1730_);
lean_ctor_set(v___x_1736_, 1, v_currRecDepth_1731_);
lean_ctor_set(v___x_1736_, 2, v_ref_1735_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*3, v_diag_1733_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*3 + 1, v_suppressElabErrors_1734_);
v___x_1737_ = l_Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0___redArg(v_msg_1724_, v___y_1725_, v___y_1726_, v___x_1736_, v___y_1728_);
lean_dec_ref_known(v___x_1736_, 3);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_1738_, lean_object* v_msg_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1738_, v_msg_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v_ref_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(lean_object* v_ref_1746_, lean_object* v_msg_1747_, lean_object* v_declHint_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_1747_, v_declHint_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_1746_, v_a_1755_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v_declHint_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1757_, v_msg_1758_, v_declHint_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v_ref_1757_);
return v_res_1765_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__2));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_ref_1772_, lean_object* v_constName_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1779_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__1);
v___x_1780_ = 0;
lean_inc(v_constName_1773_);
v___x_1781_ = l_Lean_MessageData_ofConstName(v_constName_1773_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___closed__3);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_1772_, v___x_1784_, v_constName_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_ref_1786_, lean_object* v_constName_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1786_, v_constName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_ref_1786_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(lean_object* v_constName_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_ref_1800_; lean_object* v___x_1801_; 
v_ref_1800_ = lean_ctor_get(v___y_1797_, 2);
v___x_1801_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_1800_, v_constName_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_constName_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(lean_object* v_constName_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v_env_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = lean_st_ref_get(v___y_1813_);
v_env_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc_ref(v_env_1816_);
lean_dec(v___x_1815_);
v___x_1817_ = 0;
lean_inc(v_constName_1809_);
v___x_1818_ = l_Lean_Environment_find_x3f(v_env_1816_, v_constName_1809_, v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_constName_1809_);
v_val_1820_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1818_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_val_1820_);
lean_dec(v___x_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_val_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0___boxed(lean_object* v_constName_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_constName_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(lean_object* v_declName_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
lean_inc(v_declName_1835_);
v___x_1842_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0(v_declName_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1868_; 
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v___x_1842_, 0);
lean_dec(v_unused_1869_);
v___x_1844_ = v___x_1842_;
v_isShared_1845_ = v_isSharedCheck_1868_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v___x_1842_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1868_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v_env_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_st_ref_get(v___y_1839_);
v_env_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_ref(v_env_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1847_, v_declName_1835_);
lean_dec(v_declName_1835_);
lean_dec_ref(v_env_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_box(0);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1849_);
v___x_1851_ = v___x_1844_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1867_; 
v_val_1853_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1855_ = v___x_1848_;
v_isShared_1856_ = v_isSharedCheck_1867_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v___x_1848_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1867_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v_env_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1857_ = lean_st_ref_get(v___y_1839_);
v_env_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc_ref(v_env_1858_);
lean_dec(v___x_1857_);
v___x_1859_ = l_Lean_Environment_allImportedModuleNames(v_env_1858_);
lean_dec_ref(v_env_1858_);
v___x_1860_ = lean_array_get(v___x_1841_, v___x_1859_, v_val_1853_);
lean_dec(v_val_1853_);
lean_dec_ref(v___x_1859_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1860_);
v___x_1862_ = v___x_1855_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1862_);
v___x_1864_ = v___x_1844_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_declName_1835_);
v_a_1870_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1842_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1842_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
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
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0___boxed(lean_object* v_declName_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_declName_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(lean_object* v_init_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v_k_1892_; lean_object* v_l_1893_; lean_object* v_r_1894_; lean_object* v___x_1895_; 
v_k_1892_ = lean_ctor_get(v_x_1886_, 1);
lean_inc(v_k_1892_);
v_l_1893_ = lean_ctor_get(v_x_1886_, 3);
lean_inc(v_l_1893_);
v_r_1894_ = lean_ctor_get(v_x_1886_, 4);
lean_inc(v_r_1894_);
lean_dec_ref_known(v_x_1886_, 5);
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1885_, v_l_1893_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l_Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0(v_k_1892_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = lean_array_push(v_a_1896_, v_a_1898_);
v_init_1885_ = v___x_1899_;
v_x_1886_ = v_r_1894_;
goto _start;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1896_);
lean_dec(v_r_1894_);
v_a_1901_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1897_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1897_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_dec(v_r_1894_);
lean_dec(v_k_1892_);
return v___x_1895_;
}
}
else
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_init_1885_);
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3___boxed(lean_object* v_init_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v_init_1910_, v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1917_;
}
}
static lean_object* _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = l_Lean_NameSet_empty;
v___x_1920_ = lean_obj_once(&l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1, &l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1_once, _init_l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr___closed__1);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(lean_object* v_pre_1922_, lean_object* v_type_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___f_1929_; lean_object* v___y_1931_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___f_1929_ = ((lean_object*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__0));
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_obj_once(&l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1, &l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1_once, _init_l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___closed__1);
v___x_1939_ = lean_st_mk_ref(v___x_1938_);
lean_inc_ref(v_type_1923_);
v___x_1940_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseName(v_type_1923_, v___x_1939_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v_consts_1946_; lean_object* v___x_1947_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1959_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = lean_st_ref_get(v___x_1939_);
lean_dec(v___x_1939_);
v___x_1943_ = lean_string_append(v_pre_1922_, v_a_1941_);
lean_dec(v_a_1941_);
v___x_1944_ = l_Lean_getMainModule___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__1___redArg(v_a_1927_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v_consts_1946_ = lean_ctor_get(v___x_1942_, 1);
lean_inc(v_consts_1946_);
lean_dec(v___x_1942_);
v___x_1947_ = l_Lean_Name_getRoot(v_a_1945_);
lean_dec(v_a_1945_);
if (lean_obj_tag(v_consts_1946_) == 0)
{
lean_object* v_size_1976_; 
v_size_1976_ = lean_ctor_get(v_consts_1946_, 0);
lean_inc(v_size_1976_);
v___y_1959_ = v_size_1976_;
goto v___jp_1958_;
}
else
{
v___y_1959_ = v___x_1937_;
goto v___jp_1958_;
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_moduleToSuffix(v___x_1947_);
v___x_1950_ = lean_string_append(v___x_1943_, v___x_1949_);
lean_dec_ref(v___x_1949_);
v___y_1931_ = v___x_1950_;
goto v___jp_1930_;
}
v___jp_1951_:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_lt(v___x_1937_, v___y_1952_);
if (v___x_1954_ == 0)
{
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
goto v___jp_1948_;
}
else
{
if (v___x_1954_ == 0)
{
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
goto v___jp_1948_;
}
else
{
size_t v___x_1955_; size_t v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_of_nat(v___y_1952_);
lean_dec(v___y_1952_);
lean_inc(v___x_1947_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__4(v___x_1947_, v___y_1953_, v___x_1955_, v___x_1956_);
lean_dec_ref(v___y_1953_);
if (v___x_1957_ == 0)
{
goto v___jp_1948_;
}
else
{
lean_dec(v___x_1947_);
v___y_1931_ = v___x_1943_;
goto v___jp_1930_;
}
}
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_mk_empty_array_with_capacity(v___y_1959_);
lean_dec(v___y_1959_);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__3(v___x_1960_, v_consts_1946_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = lean_array_get_size(v_a_1962_);
v___x_1964_ = lean_nat_dec_lt(v___x_1937_, v___x_1963_);
if (v___x_1964_ == 0)
{
v___y_1952_ = v___x_1963_;
v___y_1953_ = v_a_1962_;
goto v___jp_1951_;
}
else
{
if (v___x_1964_ == 0)
{
v___y_1952_ = v___x_1963_;
v___y_1953_ = v_a_1962_;
goto v___jp_1951_;
}
else
{
size_t v___x_1965_; size_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = lean_usize_of_nat(v___x_1963_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__5(v_a_1962_, v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
v___y_1952_ = v___x_1963_;
v___y_1953_ = v_a_1962_;
goto v___jp_1951_;
}
else
{
lean_dec(v_a_1962_);
lean_dec(v___x_1947_);
v___y_1931_ = v___x_1943_;
goto v___jp_1930_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___x_1947_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_type_1923_);
v_a_1968_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1961_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1961_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v___x_1939_);
lean_dec_ref(v_type_1923_);
lean_dec_ref(v_pre_1922_);
v_a_1977_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1940_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1940_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
v___jp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = l_Lean_Name_str___override(v___x_1932_, v___y_1931_);
v___x_1934_ = lean_find_expr(v___f_1929_, v_type_1923_);
lean_dec_ref(v_type_1923_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; 
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l_Lean_Core_mkFreshUserName(v___x_1933_, v_a_1926_, v_a_1927_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix___boxed(lean_object* v_pre_1985_, lean_object* v_type_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_1985_, v_type_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1993_, lean_object* v_constName_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___redArg(v_constName_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_constName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3(v_00_u03b1_2001_, v_constName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b1_2009_, lean_object* v_ref_2010_, lean_object* v_constName_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_2010_, v_constName_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_ref_2019_, lean_object* v_constName_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_2018_, v_ref_2019_, v_constName_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_ref_2019_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_2027_, lean_object* v_ref_2028_, lean_object* v_msg_2029_, lean_object* v_declHint_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___redArg(v_ref_2028_, v_msg_2029_, v_declHint_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_2037_, lean_object* v_ref_2038_, lean_object* v_msg_2039_, lean_object* v_declHint_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8(v_00_u03b1_2037_, v_ref_2038_, v_msg_2039_, v_declHint_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_ref_2038_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_2047_, lean_object* v_declHint_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_2047_, v_declHint_2048_, v___y_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_2055_, lean_object* v_declHint_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10(v_msg_2055_, v_declHint_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_2063_, lean_object* v_ref_2064_, lean_object* v_msg_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___redArg(v_ref_2064_, v_msg_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_ref_2073_, lean_object* v_msg_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__10(v_00_u03b1_2072_, v_ref_2073_, v_msg_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_ref_2073_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(lean_object* v_a_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg___boxed(lean_object* v_a_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___redArg(v_a_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(lean_object* v_00_u03b1_2099_, lean_object* v_a_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__0(v_00_u03b1_2109_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(lean_object* v_type_2119_, lean_object* v_binds_2120_, lean_object* v_pre_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Elab_Term_elabType(v_type_2119_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; uint8_t v___x_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = 0;
v___x_2132_ = 1;
v___x_2133_ = 1;
v___x_2134_ = l_Lean_Meta_mkForallFVars(v_binds_2120_, v_a_2130_, v___x_2131_, v___x_2132_, v___x_2132_, v___x_2133_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix(v_pre_2121_, v_a_2135_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_pre_2121_);
v_a_2137_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2134_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2134_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_pre_2121_);
v_a_2145_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2129_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2129_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed(lean_object* v_type_2153_, lean_object* v_binds_2154_, lean_object* v_pre_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0(v_type_2153_, v_binds_2154_, v_pre_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_binds_2154_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(lean_object* v_type_2164_, lean_object* v_pre_2165_, lean_object* v_binds_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___f_2174_; lean_object* v___x_2175_; 
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2174_, 0, v_type_2164_);
lean_closure_set(v___f_2174_, 1, v_binds_2166_);
lean_closure_set(v___f_2174_, 2, v_pre_2165_);
v___x_2175_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_2174_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed(lean_object* v_type_2176_, lean_object* v_pre_2177_, lean_object* v_binds_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1(v_type_2176_, v_pre_2177_, v_binds_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(lean_object* v_currNamespace_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_currNamespace_2187_);
lean_ctor_set(v___x_2190_, 1, v___y_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3(v_currNamespace_2191_, v___y_2192_, v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(lean_object* v_env_2195_, lean_object* v_declName_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v___x_2199_; lean_object* v_env_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2199_ = 0;
v_env_2200_ = l_Lean_Environment_setExporting(v_env_2195_, v___x_2199_);
lean_inc(v_declName_2196_);
v___x_2201_ = l_Lean_mkPrivateName(v_env_2200_, v_declName_2196_);
v___x_2202_ = 1;
lean_inc_ref(v_env_2200_);
v___x_2203_ = l_Lean_Environment_contains(v_env_2200_, v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = l_Lean_privateToUserName(v_declName_2196_);
v___x_2205_ = l_Lean_Environment_contains(v_env_2200_, v___x_2204_, v___x_2202_);
v___x_2206_ = lean_box(v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___y_2198_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_env_2200_);
lean_dec(v_declName_2196_);
v___x_2208_ = lean_box(v___x_2203_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___y_2198_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed(lean_object* v_env_2210_, lean_object* v_declName_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1(v_env_2210_, v_declName_2211_, v___y_2212_, v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(lean_object* v_x_2215_, lean_object* v___y_2216_){
_start:
{
if (lean_obj_tag(v_x_2215_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_a_2217_);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_a_2217_);
lean_ctor_set(v___x_2218_, 1, v___y_2216_);
return v___x_2218_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
v_a_2219_ = lean_ctor_get(v_x_2215_, 0);
lean_inc(v_a_2219_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v_a_2219_);
lean_ctor_set(v___x_2220_, 1, v___y_2216_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg___boxed(lean_object* v_x_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_2221_, v___y_2222_);
lean_dec_ref(v_x_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(lean_object* v_env_2224_, lean_object* v_stx_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2224_, v_stx_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
if (lean_obj_tag(v_a_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_a_2230_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v___x_2228_, 0);
lean_dec(v_unused_2239_);
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(0);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_a_2230_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2268_; 
v_val_2240_ = lean_ctor_get(v_a_2229_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2242_ = v_a_2229_;
v_isShared_2243_ = v_isSharedCheck_2268_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_val_2240_);
lean_dec(v_a_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2268_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_snd_2244_; 
v_snd_2244_ = lean_ctor_get(v_val_2240_, 1);
lean_inc(v_snd_2244_);
lean_dec(v_val_2240_);
if (lean_obj_tag(v_snd_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2254_; 
lean_del_object(v___x_2242_);
v_a_2245_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2228_, 2);
v_a_2246_ = lean_ctor_get(v_snd_2244_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_snd_2244_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2248_ = v_snd_2244_;
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v_snd_2244_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2251_, v_a_2245_);
lean_dec_ref(v___x_2251_);
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2267_; 
v_a_2255_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2228_, 2);
v_a_2256_ = lean_ctor_get(v_snd_2244_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_snd_2244_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2258_ = v_snd_2244_;
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v_snd_2244_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v_a_2256_);
v___x_2261_ = v___x_2242_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v___x_2263_, v_a_2255_);
lean_dec_ref(v___x_2263_);
return v___x_2264_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2269_ = lean_ctor_get(v___x_2228_, 0);
v_a_2270_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2228_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_inc(v_a_2269_);
lean_dec(v___x_2228_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2269_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed(lean_object* v_env_2278_, lean_object* v_stx_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0(v_env_2278_, v_stx_2279_, v___y_2280_, v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(lean_object* v_opts_2283_, lean_object* v_opt_2284_){
_start:
{
lean_object* v_name_2285_; lean_object* v_defValue_2286_; lean_object* v_map_2287_; lean_object* v___x_2288_; 
v_name_2285_ = lean_ctor_get(v_opt_2284_, 0);
v_defValue_2286_ = lean_ctor_get(v_opt_2284_, 1);
v_map_2287_ = lean_ctor_get(v_opts_2283_, 0);
v___x_2288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2287_, v_name_2285_);
if (lean_obj_tag(v___x_2288_) == 0)
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_unbox(v_defValue_2286_);
return v___x_2289_;
}
else
{
lean_object* v_val_2290_; 
v_val_2290_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2290_);
lean_dec_ref_known(v___x_2288_, 1);
if (lean_obj_tag(v_val_2290_) == 1)
{
uint8_t v_v_2291_; 
v_v_2291_ = lean_ctor_get_uint8(v_val_2290_, 0);
lean_dec_ref_known(v_val_2290_, 0);
return v_v_2291_;
}
else
{
uint8_t v___x_2292_; 
lean_dec(v_val_2290_);
v___x_2292_ = lean_unbox(v_defValue_2286_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* v_opts_2293_, lean_object* v_opt_2294_){
_start:
{
uint8_t v_res_2295_; lean_object* v_r_2296_; 
v_res_2295_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_opts_2293_, v_opt_2294_);
lean_dec_ref(v_opt_2294_);
lean_dec_ref(v_opts_2293_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_box(1);
v___x_2298_ = l_Lean_MessageData_ofFormat(v___x_2297_);
return v___x_2298_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__2));
v___x_2303_ = l_Lean_MessageData_ofFormat(v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(lean_object* v_x_2304_, lean_object* v_x_2305_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
return v_x_2304_;
}
else
{
lean_object* v_head_2306_; lean_object* v_tail_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2329_; 
v_head_2306_ = lean_ctor_get(v_x_2305_, 0);
v_tail_2307_ = lean_ctor_get(v_x_2305_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_x_2305_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2309_ = v_x_2305_;
v_isShared_2310_ = v_isSharedCheck_2329_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_tail_2307_);
lean_inc(v_head_2306_);
lean_dec(v_x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2329_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_before_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2327_; 
v_before_2311_ = lean_ctor_get(v_head_2306_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_head_2306_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_head_2306_, 1);
lean_dec(v_unused_2328_);
v___x_2313_ = v_head_2306_;
v_isShared_2314_ = v_isSharedCheck_2327_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_before_2311_);
lean_dec(v_head_2306_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2327_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2314_ == 0)
{
lean_ctor_set_tag(v___x_2313_, 7);
lean_ctor_set(v___x_2313_, 1, v___x_2315_);
lean_ctor_set(v___x_2313_, 0, v_x_2304_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_x_2304_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__3);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 7);
lean_ctor_set(v___x_2309_, 1, v___x_2318_);
lean_ctor_set(v___x_2309_, 0, v___x_2317_);
v___x_2320_ = v___x_2309_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = l_Lean_MessageData_ofSyntax(v_before_2311_);
v___x_2322_ = l_Lean_indentD(v___x_2321_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2320_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v_x_2304_ = v___x_2323_;
v_x_2305_ = v_tail_2307_;
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
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__1));
v___x_2334_ = l_Lean_MessageData_ofFormat(v___x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(lean_object* v_msgData_2335_, lean_object* v_macroStack_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_toCold_2339_; lean_object* v_options_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_toCold_2339_ = lean_ctor_get(v___y_2337_, 0);
v_options_2340_ = lean_ctor_get(v_toCold_2339_, 2);
v___x_2341_ = l_Lean_Elab_pp_macroStack;
v___x_2342_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__17(v_options_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; 
lean_dec(v_macroStack_2336_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_msgData_2335_);
return v___x_2343_;
}
else
{
if (lean_obj_tag(v_macroStack_2336_) == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_msgData_2335_);
return v___x_2344_;
}
else
{
lean_object* v_head_2345_; lean_object* v_after_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2361_; 
v_head_2345_ = lean_ctor_get(v_macroStack_2336_, 0);
lean_inc(v_head_2345_);
v_after_2346_ = lean_ctor_get(v_head_2345_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_head_2345_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v_head_2345_, 0);
lean_dec(v_unused_2362_);
v___x_2348_ = v_head_2345_;
v_isShared_2349_ = v_isSharedCheck_2361_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_after_2346_);
lean_dec(v_head_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2361_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18___closed__0);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 7);
lean_ctor_set(v___x_2348_, 1, v___x_2350_);
lean_ctor_set(v___x_2348_, 0, v_msgData_2335_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_msgData_2335_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v_msgData_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2353_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___closed__2);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = l_Lean_MessageData_ofSyntax(v_after_2346_);
v___x_2356_ = l_Lean_indentD(v___x_2355_);
v_msgData_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2357_, 0, v___x_2354_);
lean_ctor_set(v_msgData_2357_, 1, v___x_2356_);
v___x_2358_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15_spec__18(v_msgData_2357_, v_macroStack_2336_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_msgData_2363_, lean_object* v_macroStack_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_2363_, v_macroStack_2364_, v___y_2365_);
lean_dec_ref(v___y_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(lean_object* v_msg_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_ref_2376_; lean_object* v_macroStack_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2390_; 
v_ref_2376_ = lean_ctor_get(v___y_2373_, 2);
v_macroStack_2377_ = lean_ctor_get(v___y_2369_, 1);
v___x_2378_ = l_Lean_Elab_getBetterRef(v_ref_2376_, v_macroStack_2377_);
v___x_2379_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2368_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref(v___x_2379_);
lean_inc(v_macroStack_2377_);
v___x_2381_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_a_2380_, v_macroStack_2377_, v___y_2373_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2378_);
lean_ctor_set(v___x_2386_, 1, v_a_2382_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_msg_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(lean_object* v_ref_2400_, lean_object* v_msg_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_toCold_2409_; lean_object* v_currRecDepth_2410_; lean_object* v_ref_2411_; uint8_t v_diag_2412_; uint8_t v_suppressElabErrors_2413_; lean_object* v_ref_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_toCold_2409_ = lean_ctor_get(v___y_2406_, 0);
v_currRecDepth_2410_ = lean_ctor_get(v___y_2406_, 1);
v_ref_2411_ = lean_ctor_get(v___y_2406_, 2);
v_diag_2412_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*3);
v_suppressElabErrors_2413_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*3 + 1);
v_ref_2414_ = l_Lean_replaceRef(v_ref_2400_, v_ref_2411_);
lean_inc(v_currRecDepth_2410_);
lean_inc_ref(v_toCold_2409_);
v___x_2415_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2415_, 0, v_toCold_2409_);
lean_ctor_set(v___x_2415_, 1, v_currRecDepth_2410_);
lean_ctor_set(v___x_2415_, 2, v_ref_2414_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*3, v_diag_2412_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*3 + 1, v_suppressElabErrors_2413_);
v___x_2416_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___x_2415_, v___y_2407_);
lean_dec_ref_known(v___x_2415_, 3);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2417_, lean_object* v_msg_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_2417_, v_msg_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v_ref_2417_);
return v_res_2426_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2427_; double v___x_2428_; 
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = lean_float_of_nat(v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(lean_object* v_cls_2431_, lean_object* v_msg_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_ref_2438_; lean_object* v___x_2439_; lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2484_; 
v_ref_2438_ = lean_ctor_get(v___y_2435_, 2);
v___x_2439_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_winnowExpr_visit_spec__0_spec__0(v_msg_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2484_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2484_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v_traceState_2445_; lean_object* v_env_2446_; lean_object* v_nextMacroScope_2447_; lean_object* v_ngen_2448_; lean_object* v_auxDeclNGen_2449_; lean_object* v_cache_2450_; lean_object* v_messages_2451_; lean_object* v_infoState_2452_; lean_object* v_snapshotTasks_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2483_; 
v___x_2444_ = lean_st_ref_take(v___y_2436_);
v_traceState_2445_ = lean_ctor_get(v___x_2444_, 4);
v_env_2446_ = lean_ctor_get(v___x_2444_, 0);
v_nextMacroScope_2447_ = lean_ctor_get(v___x_2444_, 1);
v_ngen_2448_ = lean_ctor_get(v___x_2444_, 2);
v_auxDeclNGen_2449_ = lean_ctor_get(v___x_2444_, 3);
v_cache_2450_ = lean_ctor_get(v___x_2444_, 5);
v_messages_2451_ = lean_ctor_get(v___x_2444_, 6);
v_infoState_2452_ = lean_ctor_get(v___x_2444_, 7);
v_snapshotTasks_2453_ = lean_ctor_get(v___x_2444_, 8);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2455_ = v___x_2444_;
v_isShared_2456_ = v_isSharedCheck_2483_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snapshotTasks_2453_);
lean_inc(v_infoState_2452_);
lean_inc(v_messages_2451_);
lean_inc(v_cache_2450_);
lean_inc(v_traceState_2445_);
lean_inc(v_auxDeclNGen_2449_);
lean_inc(v_ngen_2448_);
lean_inc(v_nextMacroScope_2447_);
lean_inc(v_env_2446_);
lean_dec(v___x_2444_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2483_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
uint64_t v_tid_2457_; lean_object* v_traces_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2482_; 
v_tid_2457_ = lean_ctor_get_uint64(v_traceState_2445_, sizeof(void*)*1);
v_traces_2458_ = lean_ctor_get(v_traceState_2445_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_traceState_2445_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2460_ = v_traceState_2445_;
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_traces_2458_);
lean_dec(v_traceState_2445_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2482_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; double v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__0);
v___x_2465_ = 0;
v___x_2466_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2467_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2467_, 0, v_cls_2431_);
lean_ctor_set(v___x_2467_, 1, v___x_2463_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
lean_ctor_set_float(v___x_2467_, sizeof(void*)*3, v___x_2464_);
lean_ctor_set_float(v___x_2467_, sizeof(void*)*3 + 8, v___x_2464_);
lean_ctor_set_uint8(v___x_2467_, sizeof(void*)*3 + 16, v___x_2465_);
v___x_2468_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___closed__1));
v___x_2469_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v_a_2440_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
lean_inc(v_ref_2438_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_ref_2438_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_PersistentArray_push___redArg(v_traces_2458_, v___x_2470_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2471_);
v___x_2473_ = v___x_2460_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2471_);
lean_ctor_set_uint64(v_reuseFailAlloc_2481_, sizeof(void*)*1, v_tid_2457_);
v___x_2473_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 4, v___x_2473_);
v___x_2475_ = v___x_2455_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_env_2446_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2447_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2448_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2449_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v_cache_2450_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_messages_2451_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_infoState_2452_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_snapshotTasks_2453_);
v___x_2475_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = lean_st_ref_put(v___y_2436_, v___x_2475_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2462_);
v___x_2478_ = v___x_2442_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2462_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2485_, lean_object* v_msg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2485_, v_msg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(lean_object* v_as_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
if (lean_obj_tag(v_as_2496_) == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
else
{
lean_object* v_toCold_2506_; lean_object* v_options_2507_; uint8_t v_hasTrace_2508_; 
v_toCold_2506_ = lean_ctor_get(v___y_2501_, 0);
v_options_2507_ = lean_ctor_get(v_toCold_2506_, 2);
v_hasTrace_2508_ = lean_ctor_get_uint8(v_options_2507_, sizeof(void*)*1);
if (v_hasTrace_2508_ == 0)
{
lean_object* v_tail_2509_; 
v_tail_2509_ = lean_ctor_get(v_as_2496_, 1);
lean_inc(v_tail_2509_);
lean_dec_ref_known(v_as_2496_, 2);
v_as_2496_ = v_tail_2509_;
goto _start;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v_inheritedTraceOptions_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_head_2511_ = lean_ctor_get(v_as_2496_, 0);
lean_inc(v_head_2511_);
v_tail_2512_ = lean_ctor_get(v_as_2496_, 1);
lean_inc(v_tail_2512_);
lean_dec_ref_known(v_as_2496_, 2);
v_fst_2513_ = lean_ctor_get(v_head_2511_, 0);
lean_inc_n(v_fst_2513_, 2);
v_snd_2514_ = lean_ctor_get(v_head_2511_, 1);
lean_inc(v_snd_2514_);
lean_dec(v_head_2511_);
v_inheritedTraceOptions_2515_ = lean_ctor_get(v_toCold_2506_, 11);
v___x_2516_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2517_ = l_Lean_Name_append(v___x_2516_, v_fst_2513_);
v___x_2518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2515_, v_options_2507_, v___x_2517_);
lean_dec(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_dec(v_snd_2514_);
lean_dec(v_fst_2513_);
v_as_2496_ = v_tail_2512_;
goto _start;
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_snd_2514_);
v___x_2521_ = l_Lean_MessageData_ofFormat(v___x_2520_);
v___x_2522_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_fst_2513_, v___x_2521_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v_as_2496_ = v_tail_2512_;
goto _start;
}
else
{
lean_dec(v_tail_2512_);
return v___x_2522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___boxed(lean_object* v_as_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v_as_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* v_keys_2533_, lean_object* v_i_2534_, lean_object* v_k_2535_){
_start:
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_array_get_size(v_keys_2533_);
v___x_2537_ = lean_nat_dec_lt(v_i_2534_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec(v_i_2534_);
return v___x_2537_;
}
else
{
lean_object* v_k_x27_2538_; uint8_t v___x_2539_; 
v_k_x27_2538_ = lean_array_fget_borrowed(v_keys_2533_, v_i_2534_);
v___x_2539_ = l_Lean_instBEqExtraModUse_beq(v_k_2535_, v_k_x27_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_unsigned_to_nat(1u);
v___x_2541_ = lean_nat_add(v_i_2534_, v___x_2540_);
lean_dec(v_i_2534_);
v_i_2534_ = v___x_2541_;
goto _start;
}
else
{
lean_dec(v_i_2534_);
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* v_keys_2543_, lean_object* v_i_2544_, lean_object* v_k_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_2543_, v_i_2544_, v_k_2545_);
lean_dec_ref(v_k_2545_);
lean_dec_ref(v_keys_2543_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_x_2548_, size_t v_x_2549_, lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2548_) == 0)
{
lean_object* v_es_2551_; lean_object* v___x_2552_; size_t v___x_2553_; size_t v___x_2554_; lean_object* v_j_2555_; lean_object* v___x_2556_; 
v_es_2551_ = lean_ctor_get(v_x_2548_, 0);
v___x_2552_ = lean_box(2);
v___x_2553_ = ((size_t)31ULL);
v___x_2554_ = lean_usize_land(v_x_2549_, v___x_2553_);
v_j_2555_ = lean_usize_to_nat(v___x_2554_);
v___x_2556_ = lean_array_get_borrowed(v___x_2552_, v_es_2551_, v_j_2555_);
lean_dec(v_j_2555_);
switch(lean_obj_tag(v___x_2556_))
{
case 0:
{
lean_object* v_key_2557_; uint8_t v___x_2558_; 
v_key_2557_ = lean_ctor_get(v___x_2556_, 0);
v___x_2558_ = l_Lean_instBEqExtraModUse_beq(v_x_2550_, v_key_2557_);
return v___x_2558_;
}
case 1:
{
lean_object* v_node_2559_; size_t v___x_2560_; size_t v___x_2561_; 
v_node_2559_ = lean_ctor_get(v___x_2556_, 0);
v___x_2560_ = ((size_t)5ULL);
v___x_2561_ = lean_usize_shift_right(v_x_2549_, v___x_2560_);
v_x_2548_ = v_node_2559_;
v_x_2549_ = v___x_2561_;
goto _start;
}
default: 
{
uint8_t v___x_2563_; 
v___x_2563_ = 0;
return v___x_2563_;
}
}
}
else
{
lean_object* v_ks_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_ks_2564_ = lean_ctor_get(v_x_2548_, 0);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_ks_2564_, v___x_2565_, v_x_2550_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
size_t v_x_14631__boxed_2570_; uint8_t v_res_2571_; lean_object* v_r_2572_; 
v_x_14631__boxed_2570_ = lean_unbox_usize(v_x_2568_);
lean_dec(v_x_2568_);
v_res_2571_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2567_, v_x_14631__boxed_2570_, v_x_2569_);
lean_dec_ref(v_x_2569_);
lean_dec_ref(v_x_2567_);
v_r_2572_ = lean_box(v_res_2571_);
return v_r_2572_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2573_, lean_object* v_x_2574_){
_start:
{
uint64_t v___x_2575_; size_t v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = l_Lean_instHashableExtraModUse_hash(v_x_2574_);
v___x_2576_ = lean_uint64_to_usize(v___x_2575_);
v___x_2577_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_2573_, v___x_2576_, v_x_2574_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
uint8_t v_res_2580_; lean_object* v_r_2581_; 
v_res_2580_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_2578_, v_x_2579_);
lean_dec_ref(v_x_2579_);
lean_dec_ref(v_x_2578_);
v_r_2581_ = lean_box(v_res_2580_);
return v_r_2581_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2582_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__1);
v___x_2588_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
lean_ctor_set(v___x_2588_, 2, v___x_2587_);
lean_ctor_set(v___x_2588_, 3, v___x_2587_);
lean_ctor_set(v___x_2588_, 4, v___x_2587_);
lean_ctor_set(v___x_2588_, 5, v___x_2587_);
return v___x_2588_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__6));
v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
return v___x_2594_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__8));
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
return v___x_2597_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_Elab_DeclNameGen_0__Lean_Elab_Command_NameGen_mkBaseNameCore_visit___closed__0));
v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11(void){
_start:
{
lean_object* v_cls_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_cls_2600_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2601_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5___closed__1));
v___x_2602_ = l_Lean_Name_append(v___x_2601_, v_cls_2600_);
return v___x_2602_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__12));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__14));
v___x_2608_ = l_Lean_stringToMessageData(v___x_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(lean_object* v_mod_2613_, uint8_t v_isMeta_2614_, lean_object* v_hint_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_env_2625_; uint8_t v_isExporting_2626_; lean_object* v_entry_2627_; lean_object* v___x_2628_; lean_object* v_env_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__0);
v___x_2624_ = lean_st_ref_get(v___y_2621_);
v_env_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc_ref(v_env_2625_);
lean_dec(v___x_2624_);
v_isExporting_2626_ = lean_ctor_get_uint8(v_env_2625_, sizeof(void*)*8);
lean_dec_ref(v_env_2625_);
lean_inc(v_mod_2613_);
v_entry_2627_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2627_, 0, v_mod_2613_);
lean_ctor_set_uint8(v_entry_2627_, sizeof(void*)*1, v_isExporting_2626_);
lean_ctor_set_uint8(v_entry_2627_, sizeof(void*)*1 + 1, v_isMeta_2614_);
v___x_2628_ = lean_st_ref_get(v___y_2621_);
v_env_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_ref(v_env_2629_);
lean_dec(v___x_2628_);
v___x_2630_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2631_ = lean_box(1);
v___x_2632_ = lean_box(0);
v___x_2675_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2623_, v___x_2630_, v_env_2629_, v___x_2631_, v___x_2632_);
v___x_2676_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v___x_2675_, v_entry_2627_);
lean_dec(v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v_toCold_2677_; lean_object* v_options_2678_; uint8_t v_hasTrace_2679_; 
v_toCold_2677_ = lean_ctor_get(v___y_2620_, 0);
v_options_2678_ = lean_ctor_get(v_toCold_2677_, 2);
v_hasTrace_2679_ = lean_ctor_get_uint8(v_options_2678_, sizeof(void*)*1);
if (v_hasTrace_2679_ == 0)
{
lean_dec(v_hint_2615_);
lean_dec(v_mod_2613_);
v___y_2634_ = v___y_2619_;
v___y_2635_ = v___y_2621_;
goto v___jp_2633_;
}
else
{
lean_object* v_inheritedTraceOptions_2680_; lean_object* v_cls_2681_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_inheritedTraceOptions_2680_ = lean_ctor_get(v_toCold_2677_, 11);
v_cls_2681_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__5));
v___x_2701_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__11);
v___x_2702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2680_, v_options_2678_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_dec(v_hint_2615_);
lean_dec(v_mod_2613_);
v___y_2634_ = v___y_2619_;
v___y_2635_ = v___y_2621_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2703_; lean_object* v___y_2705_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__13);
if (v_isExporting_2626_ == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__18));
v___y_2705_ = v___x_2712_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__19));
v___y_2705_ = v___x_2713_;
goto v___jp_2704_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc_ref(v___y_2705_);
v___x_2706_ = l_Lean_stringToMessageData(v___y_2705_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2703_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__15);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
if (v_isMeta_2614_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__16));
v___y_2688_ = v___x_2709_;
v___y_2689_ = v___x_2710_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2711_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__17));
v___y_2688_ = v___x_2709_;
v___y_2689_ = v___x_2711_;
goto v___jp_2687_;
}
}
}
v___jp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___y_2683_);
lean_ctor_set(v___x_2685_, 1, v___y_2684_);
v___x_2686_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_2681_, v___x_2685_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_dec_ref_known(v___x_2686_, 1);
v___y_2634_ = v___y_2619_;
v___y_2635_ = v___y_2621_;
goto v___jp_2633_;
}
else
{
lean_dec_ref_known(v_entry_2627_, 1);
return v___x_2686_;
}
}
v___jp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
lean_inc_ref(v___y_2689_);
v___x_2690_ = l_Lean_stringToMessageData(v___y_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__7);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_MessageData_ofName(v_mod_2613_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_Name_isAnonymous(v_hint_2615_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__9);
v___x_2698_ = l_Lean_MessageData_ofName(v_hint_2615_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___y_2683_ = v___x_2695_;
v___y_2684_ = v___x_2699_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_hint_2615_);
v___x_2700_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__10);
v___y_2683_ = v___x_2695_;
v___y_2684_ = v___x_2700_;
goto v___jp_2682_;
}
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref_known(v_entry_2627_, 1);
lean_dec(v_hint_2615_);
lean_dec(v_mod_2613_);
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
v___jp_2633_:
{
lean_object* v___x_2636_; lean_object* v_toEnvExtension_2637_; lean_object* v_env_2638_; lean_object* v_nextMacroScope_2639_; lean_object* v_ngen_2640_; lean_object* v_auxDeclNGen_2641_; lean_object* v_traceState_2642_; lean_object* v_messages_2643_; lean_object* v_infoState_2644_; lean_object* v_snapshotTasks_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2673_; 
v___x_2636_ = lean_st_ref_take(v___y_2635_);
v_toEnvExtension_2637_ = lean_ctor_get(v___x_2630_, 0);
v_env_2638_ = lean_ctor_get(v___x_2636_, 0);
v_nextMacroScope_2639_ = lean_ctor_get(v___x_2636_, 1);
v_ngen_2640_ = lean_ctor_get(v___x_2636_, 2);
v_auxDeclNGen_2641_ = lean_ctor_get(v___x_2636_, 3);
v_traceState_2642_ = lean_ctor_get(v___x_2636_, 4);
v_messages_2643_ = lean_ctor_get(v___x_2636_, 6);
v_infoState_2644_ = lean_ctor_get(v___x_2636_, 7);
v_snapshotTasks_2645_ = lean_ctor_get(v___x_2636_, 8);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2636_, 5);
lean_dec(v_unused_2674_);
v___x_2647_ = v___x_2636_;
v_isShared_2648_ = v_isSharedCheck_2673_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_snapshotTasks_2645_);
lean_inc(v_infoState_2644_);
lean_inc(v_messages_2643_);
lean_inc(v_traceState_2642_);
lean_inc(v_auxDeclNGen_2641_);
lean_inc(v_ngen_2640_);
lean_inc(v_nextMacroScope_2639_);
lean_inc(v_env_2638_);
lean_dec(v___x_2636_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2673_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_asyncMode_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v_asyncMode_2649_ = lean_ctor_get(v_toEnvExtension_2637_, 2);
v___x_2650_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2630_, v_env_2638_, v_entry_2627_, v_asyncMode_2649_, v___x_2632_);
v___x_2651_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__2);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 5, v___x_2651_);
lean_ctor_set(v___x_2647_, 0, v___x_2650_);
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_nextMacroScope_2639_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_ngen_2640_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_auxDeclNGen_2641_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v_traceState_2642_);
lean_ctor_set(v_reuseFailAlloc_2672_, 5, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2672_, 6, v_messages_2643_);
lean_ctor_set(v_reuseFailAlloc_2672_, 7, v_infoState_2644_);
lean_ctor_set(v_reuseFailAlloc_2672_, 8, v_snapshotTasks_2645_);
v___x_2653_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_mctx_2656_; lean_object* v_zetaDeltaFVarIds_2657_; lean_object* v_postponed_2658_; lean_object* v_diag_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2670_; 
v___x_2654_ = lean_st_ref_put(v___y_2635_, v___x_2653_);
v___x_2655_ = lean_st_ref_take(v___y_2634_);
v_mctx_2656_ = lean_ctor_get(v___x_2655_, 0);
v_zetaDeltaFVarIds_2657_ = lean_ctor_get(v___x_2655_, 2);
v_postponed_2658_ = lean_ctor_get(v___x_2655_, 3);
v_diag_2659_ = lean_ctor_get(v___x_2655_, 4);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2655_, 1);
lean_dec(v_unused_2671_);
v___x_2661_ = v___x_2655_;
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_diag_2659_);
lean_inc(v_postponed_2658_);
lean_inc(v_zetaDeltaFVarIds_2657_);
lean_inc(v_mctx_2656_);
lean_dec(v___x_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = lean_box(0);
v___x_2664_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___closed__3);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_mctx_2656_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_zetaDeltaFVarIds_2657_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_postponed_2658_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v_diag_2659_);
v___x_2666_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_st_ref_put(v___y_2634_, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2663_);
return v___x_2668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4___boxed(lean_object* v_mod_2716_, lean_object* v_isMeta_2717_, lean_object* v_hint_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_isMeta_boxed_2726_; lean_object* v_res_2727_; 
v_isMeta_boxed_2726_ = lean_unbox(v_isMeta_2717_);
v_res_2727_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_mod_2716_, v_isMeta_boxed_2726_, v_hint_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(lean_object* v___x_2728_, lean_object* v_declName_2729_, lean_object* v_as_2730_, size_t v_sz_2731_, size_t v_i_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
lean_dec(v_declName_2729_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_b_2733_);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; lean_object* v_modules_2744_; lean_object* v___x_2745_; lean_object* v_a_2746_; lean_object* v___x_2747_; lean_object* v_toImport_2748_; lean_object* v_module_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2743_ = l_Lean_Environment_header(v___x_2728_);
v_modules_2744_ = lean_ctor_get(v___x_2743_, 3);
lean_inc_ref(v_modules_2744_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2746_ = lean_array_uget_borrowed(v_as_2730_, v_i_2732_);
v___x_2747_ = lean_array_get(v___x_2745_, v_modules_2744_, v_a_2746_);
lean_dec_ref(v_modules_2744_);
v_toImport_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc_ref(v_toImport_2748_);
lean_dec(v___x_2747_);
v_module_2749_ = lean_ctor_get(v_toImport_2748_, 0);
lean_inc(v_module_2749_);
lean_dec_ref(v_toImport_2748_);
v___x_2750_ = lean_box(0);
v___x_2751_ = 0;
lean_inc(v_declName_2729_);
v___x_2752_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2749_, v___x_2751_, v_declName_2729_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2752_) == 0)
{
size_t v___x_2753_; size_t v___x_2754_; 
lean_dec_ref_known(v___x_2752_, 1);
v___x_2753_ = ((size_t)1ULL);
v___x_2754_ = lean_usize_add(v_i_2732_, v___x_2753_);
v_i_2732_ = v___x_2754_;
v_b_2733_ = v___x_2750_;
goto _start;
}
else
{
lean_dec(v_declName_2729_);
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5___boxed(lean_object* v___x_2756_, lean_object* v_declName_2757_, lean_object* v_as_2758_, lean_object* v_sz_2759_, lean_object* v_i_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
size_t v_sz_boxed_2769_; size_t v_i_boxed_2770_; lean_object* v_res_2771_; 
v_sz_boxed_2769_ = lean_unbox_usize(v_sz_2759_);
lean_dec(v_sz_2759_);
v_i_boxed_2770_ = lean_unbox_usize(v_i_2760_);
lean_dec(v_i_2760_);
v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v___x_2756_, v_declName_2757_, v_as_2758_, v_sz_boxed_2769_, v_i_boxed_2770_, v_b_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_as_2758_);
lean_dec_ref(v___x_2756_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(lean_object* v_a_2772_, lean_object* v_x_2773_){
_start:
{
if (lean_obj_tag(v_x_2773_) == 0)
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_box(0);
return v___x_2774_;
}
else
{
lean_object* v_key_2775_; lean_object* v_value_2776_; lean_object* v_tail_2777_; uint8_t v___x_2778_; 
v_key_2775_ = lean_ctor_get(v_x_2773_, 0);
v_value_2776_ = lean_ctor_get(v_x_2773_, 1);
v_tail_2777_ = lean_ctor_get(v_x_2773_, 2);
v___x_2778_ = lean_name_eq(v_key_2775_, v_a_2772_);
if (v___x_2778_ == 0)
{
v_x_2773_ = v_tail_2777_;
goto _start;
}
else
{
lean_object* v___x_2780_; 
lean_inc(v_value_2776_);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_value_2776_);
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_a_2781_, lean_object* v_x_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2781_, v_x_2782_);
lean_dec(v_x_2782_);
lean_dec(v_a_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_m_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_buckets_2786_; lean_object* v___x_2787_; uint64_t v___y_2789_; 
v_buckets_2786_ = lean_ctor_get(v_m_2784_, 1);
v___x_2787_ = lean_array_get_size(v_buckets_2786_);
if (lean_obj_tag(v_a_2785_) == 0)
{
uint64_t v___x_2803_; 
v___x_2803_ = 1723ULL;
v___y_2789_ = v___x_2803_;
goto v___jp_2788_;
}
else
{
uint64_t v_hash_2804_; 
v_hash_2804_ = lean_ctor_get_uint64(v_a_2785_, sizeof(void*)*2);
v___y_2789_ = v_hash_2804_;
goto v___jp_2788_;
}
v___jp_2788_:
{
uint64_t v___x_2790_; uint64_t v___x_2791_; uint64_t v_fold_2792_; uint64_t v___x_2793_; uint64_t v___x_2794_; uint64_t v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; size_t v___x_2798_; size_t v___x_2799_; size_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2790_ = 32ULL;
v___x_2791_ = lean_uint64_shift_right(v___y_2789_, v___x_2790_);
v_fold_2792_ = lean_uint64_xor(v___y_2789_, v___x_2791_);
v___x_2793_ = 16ULL;
v___x_2794_ = lean_uint64_shift_right(v_fold_2792_, v___x_2793_);
v___x_2795_ = lean_uint64_xor(v_fold_2792_, v___x_2794_);
v___x_2796_ = lean_uint64_to_usize(v___x_2795_);
v___x_2797_ = lean_usize_of_nat(v___x_2787_);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_sub(v___x_2797_, v___x_2798_);
v___x_2800_ = lean_usize_land(v___x_2796_, v___x_2799_);
v___x_2801_ = lean_array_uget_borrowed(v_buckets_2786_, v___x_2800_);
v___x_2802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_2785_, v___x_2801_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_m_2805_);
return v_res_2807_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(lean_object* v_declName_2811_, uint8_t v_isMeta_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_env_2825_; lean_object* v___y_2827_; lean_object* v___x_2840_; 
v___x_2820_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__0);
v___x_2821_ = lean_st_ref_get(v___y_2818_);
v_env_2825_ = lean_ctor_get(v___x_2821_, 0);
lean_inc_ref(v_env_2825_);
lean_dec(v___x_2821_);
v___x_2840_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2825_, v_declName_2811_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref(v_env_2825_);
lean_dec(v_declName_2811_);
goto v___jp_2822_;
}
else
{
lean_object* v_val_2841_; lean_object* v___x_2842_; lean_object* v_modules_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_val_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_val_2841_);
lean_dec_ref_known(v___x_2840_, 1);
v___x_2842_ = l_Lean_Environment_header(v_env_2825_);
v_modules_2843_ = lean_ctor_get(v___x_2842_, 3);
lean_inc_ref(v_modules_2843_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = lean_array_get_size(v_modules_2843_);
v___x_2845_ = lean_nat_dec_lt(v_val_2841_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_dec_ref(v_modules_2843_);
lean_dec(v_val_2841_);
lean_dec_ref(v_env_2825_);
lean_dec(v_declName_2811_);
goto v___jp_2822_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___y_2849_; 
v___x_2846_ = lean_array_fget(v_modules_2843_, v_val_2841_);
lean_dec(v_val_2841_);
lean_dec_ref(v_modules_2843_);
v___x_2847_ = lean_st_ref_get(v___y_2818_);
if (v_isMeta_2812_ == 0)
{
lean_dec(v___x_2847_);
v___y_2849_ = v_isMeta_2812_;
goto v___jp_2848_;
}
else
{
lean_object* v_env_2860_; uint8_t v___x_2861_; 
v_env_2860_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_env_2860_);
lean_dec(v___x_2847_);
lean_inc(v_declName_2811_);
v___x_2861_ = l_Lean_isMarkedMeta(v_env_2860_, v_declName_2811_);
if (v___x_2861_ == 0)
{
v___y_2849_ = v_isMeta_2812_;
goto v___jp_2848_;
}
else
{
uint8_t v___x_2862_; 
v___x_2862_ = 0;
v___y_2849_ = v___x_2862_;
goto v___jp_2848_;
}
}
v___jp_2848_:
{
lean_object* v_toImport_2850_; lean_object* v_module_2851_; lean_object* v___x_2852_; 
v_toImport_2850_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_toImport_2850_);
lean_dec(v___x_2846_);
v_module_2851_ = lean_ctor_get(v_toImport_2850_, 0);
lean_inc(v_module_2851_);
lean_dec_ref(v_toImport_2850_);
lean_inc(v_declName_2811_);
v___x_2852_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4(v_module_2851_, v___y_2849_, v_declName_2811_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec_ref_known(v___x_2852_, 1);
v___x_2853_ = l_Lean_indirectModUseExt;
v___x_2854_ = lean_box(1);
v___x_2855_ = lean_box(0);
lean_inc_ref(v_env_2825_);
v___x_2856_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2820_, v___x_2853_, v_env_2825_, v___x_2854_, v___x_2855_);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v___x_2856_, v_declName_2811_);
lean_dec(v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2858_; 
v___x_2858_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___closed__1));
v___y_2827_ = v___x_2858_;
goto v___jp_2826_;
}
else
{
lean_object* v_val_2859_; 
v_val_2859_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2827_ = v_val_2859_;
goto v___jp_2826_;
}
}
else
{
lean_dec_ref(v_env_2825_);
lean_dec(v_declName_2811_);
return v___x_2852_;
}
}
}
}
v___jp_2822_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
v___jp_2826_:
{
lean_object* v___x_2828_; size_t v_sz_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = lean_box(0);
v_sz_2829_ = lean_array_size(v___y_2827_);
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__5(v_env_2825_, v_declName_2811_, v___y_2827_, v_sz_2829_, v___x_2830_, v___x_2828_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec_ref(v___y_2827_);
lean_dec_ref(v_env_2825_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2839_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2828_);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2828_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3___boxed(lean_object* v_declName_2863_, lean_object* v_isMeta_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v_isMeta_boxed_2872_; lean_object* v_res_2873_; 
v_isMeta_boxed_2872_ = lean_unbox(v_isMeta_2864_);
v_res_2873_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_declName_2863_, v_isMeta_boxed_2872_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(lean_object* v_as_x27_2874_, lean_object* v_b_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
if (lean_obj_tag(v_as_x27_2874_) == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_b_2875_);
return v___x_2883_;
}
else
{
lean_object* v_head_2884_; lean_object* v_tail_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; 
v_head_2884_ = lean_ctor_get(v_as_x27_2874_, 0);
v_tail_2885_ = lean_ctor_get(v_as_x27_2874_, 1);
v___x_2886_ = lean_box(0);
v___x_2887_ = 1;
lean_inc(v_head_2884_);
v___x_2888_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3(v_head_2884_, v___x_2887_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_dec_ref_known(v___x_2888_, 1);
v_as_x27_2874_ = v_tail_2885_;
v_b_2875_ = v___x_2886_;
goto _start;
}
else
{
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2890_, lean_object* v_b_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_2890_, v_b_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v_as_x27_2890_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(lean_object* v_env_2900_, lean_object* v_options_2901_, lean_object* v_currNamespace_2902_, lean_object* v_openDecls_2903_, lean_object* v_n_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = l_Lean_ResolveName_resolveGlobalName(v_env_2900_, v_options_2901_, v_currNamespace_2902_, v_openDecls_2903_, v_n_2904_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___y_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed(lean_object* v_env_2909_, lean_object* v_options_2910_, lean_object* v_currNamespace_2911_, lean_object* v_openDecls_2912_, lean_object* v_n_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4(v_env_2909_, v_options_2910_, v_currNamespace_2911_, v_openDecls_2912_, v_n_2913_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v_options_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(lean_object* v_env_2917_, lean_object* v_currNamespace_2918_, lean_object* v_openDecls_2919_, lean_object* v_n_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = l_Lean_ResolveName_resolveNamespace(v_env_2917_, v_currNamespace_2918_, v_openDecls_2919_, v_n_2920_);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed(lean_object* v_env_2925_, lean_object* v_currNamespace_2926_, lean_object* v_openDecls_2927_, lean_object* v_n_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2(v_env_2925_, v_currNamespace_2926_, v_openDecls_2927_, v_n_2928_, v___y_2929_, v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v___x_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg(){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___closed__0);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg___boxed(lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v_res_2939_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = l_Lean_maxRecDepthErrorMessage;
v___x_2946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__3);
v___x_2948_ = l_Lean_MessageData_ofFormat(v___x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__4);
v___x_2950_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__2));
v___x_2951_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2949_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(lean_object* v_ref_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___closed__5);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_ref_2952_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(lean_object* v_x_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v_toCold_2970_; lean_object* v_env_2971_; lean_object* v_currRecDepth_2972_; lean_object* v_ref_2973_; lean_object* v_options_2974_; lean_object* v_maxRecDepth_2975_; lean_object* v_currNamespace_2976_; lean_object* v_openDecls_2977_; lean_object* v_quotContext_2978_; lean_object* v_currMacroScope_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___f_2983_; lean_object* v___f_2984_; lean_object* v_methods_2985_; lean_object* v___x_2986_; lean_object* v_nextMacroScope_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2969_ = lean_st_ref_get(v___y_2967_);
v_toCold_2970_ = lean_ctor_get(v___y_2966_, 0);
v_env_2971_ = lean_ctor_get(v___x_2969_, 0);
lean_inc_ref_n(v_env_2971_, 4);
lean_dec(v___x_2969_);
v_currRecDepth_2972_ = lean_ctor_get(v___y_2966_, 1);
v_ref_2973_ = lean_ctor_get(v___y_2966_, 2);
v_options_2974_ = lean_ctor_get(v_toCold_2970_, 2);
v_maxRecDepth_2975_ = lean_ctor_get(v_toCold_2970_, 3);
v_currNamespace_2976_ = lean_ctor_get(v_toCold_2970_, 4);
v_openDecls_2977_ = lean_ctor_get(v_toCold_2970_, 5);
v_quotContext_2978_ = lean_ctor_get(v_toCold_2970_, 8);
v_currMacroScope_2979_ = lean_ctor_get(v_toCold_2970_, 9);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2980_, 0, v_env_2971_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2981_, 0, v_env_2971_);
lean_inc_n(v_openDecls_2977_, 2);
lean_inc_n(v_currNamespace_2976_, 3);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2982_, 0, v_env_2971_);
lean_closure_set(v___f_2982_, 1, v_currNamespace_2976_);
lean_closure_set(v___f_2982_, 2, v_openDecls_2977_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2983_, 0, v_currNamespace_2976_);
lean_inc_ref(v_options_2974_);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2984_, 0, v_env_2971_);
lean_closure_set(v___f_2984_, 1, v_options_2974_);
lean_closure_set(v___f_2984_, 2, v_currNamespace_2976_);
lean_closure_set(v___f_2984_, 3, v_openDecls_2977_);
v_methods_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2985_, 0, v___f_2980_);
lean_ctor_set(v_methods_2985_, 1, v___f_2983_);
lean_ctor_set(v_methods_2985_, 2, v___f_2981_);
lean_ctor_set(v_methods_2985_, 3, v___f_2982_);
lean_ctor_set(v_methods_2985_, 4, v___f_2984_);
v___x_2986_ = lean_st_ref_get(v___y_2967_);
v_nextMacroScope_2987_ = lean_ctor_get(v___x_2986_, 1);
lean_inc(v_nextMacroScope_2987_);
lean_dec(v___x_2986_);
lean_inc(v_ref_2973_);
lean_inc(v_maxRecDepth_2975_);
lean_inc(v_currRecDepth_2972_);
lean_inc(v_currMacroScope_2979_);
lean_inc(v_quotContext_2978_);
v___x_2988_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2988_, 0, v_methods_2985_);
lean_ctor_set(v___x_2988_, 1, v_quotContext_2978_);
lean_ctor_set(v___x_2988_, 2, v_currMacroScope_2979_);
lean_ctor_set(v___x_2988_, 3, v_currRecDepth_2972_);
lean_ctor_set(v___x_2988_, 4, v_maxRecDepth_2975_);
lean_ctor_set(v___x_2988_, 5, v_ref_2973_);
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2990_, 0, v_nextMacroScope_2987_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
v___x_2991_ = lean_apply_2(v_x_2961_, v___x_2988_, v___x_2990_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_a_2993_; lean_object* v_macroScope_2994_; lean_object* v_traceMsgs_2995_; lean_object* v_expandedMacroDecls_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 1);
lean_inc(v_a_2992_);
v_a_2993_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2991_, 2);
v_macroScope_2994_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_macroScope_2994_);
v_traceMsgs_2995_ = lean_ctor_get(v_a_2992_, 1);
lean_inc(v_traceMsgs_2995_);
v_expandedMacroDecls_2996_ = lean_ctor_get(v_a_2992_, 2);
lean_inc(v_expandedMacroDecls_2996_);
lean_dec(v_a_2992_);
v___x_2997_ = lean_box(0);
v___x_2998_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_expandedMacroDecls_2996_, v___x_2997_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v_expandedMacroDecls_2996_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v___x_2999_; lean_object* v_env_3000_; lean_object* v_ngen_3001_; lean_object* v_auxDeclNGen_3002_; lean_object* v_traceState_3003_; lean_object* v_cache_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref_known(v___x_2998_, 1);
v___x_2999_ = lean_st_ref_take(v___y_2967_);
v_env_3000_ = lean_ctor_get(v___x_2999_, 0);
v_ngen_3001_ = lean_ctor_get(v___x_2999_, 2);
v_auxDeclNGen_3002_ = lean_ctor_get(v___x_2999_, 3);
v_traceState_3003_ = lean_ctor_get(v___x_2999_, 4);
v_cache_3004_ = lean_ctor_get(v___x_2999_, 5);
v_messages_3005_ = lean_ctor_get(v___x_2999_, 6);
v_infoState_3006_ = lean_ctor_get(v___x_2999_, 7);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_2999_, 8);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; 
v_unused_3034_ = lean_ctor_get(v___x_2999_, 1);
lean_dec(v_unused_3034_);
v___x_3009_ = v___x_2999_;
v_isShared_3010_ = v_isSharedCheck_3033_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_cache_3004_);
lean_inc(v_traceState_3003_);
lean_inc(v_auxDeclNGen_3002_);
lean_inc(v_ngen_3001_);
lean_inc(v_env_3000_);
lean_dec(v___x_2999_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3033_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v_macroScope_2994_);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_env_3000_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_macroScope_2994_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_ngen_3001_);
lean_ctor_set(v_reuseFailAlloc_3032_, 3, v_auxDeclNGen_3002_);
lean_ctor_set(v_reuseFailAlloc_3032_, 4, v_traceState_3003_);
lean_ctor_set(v_reuseFailAlloc_3032_, 5, v_cache_3004_);
lean_ctor_set(v_reuseFailAlloc_3032_, 6, v_messages_3005_);
lean_ctor_set(v_reuseFailAlloc_3032_, 7, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3032_, 8, v_snapshotTasks_3007_);
v___x_3012_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_st_ref_put(v___y_2967_, v___x_3012_);
v___x_3014_ = l_List_reverse___redArg(v_traceMsgs_2995_);
v___x_3015_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__5(v___x_3014_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3015_, 0);
lean_dec(v_unused_3023_);
v___x_3017_ = v___x_3015_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_dec(v___x_3015_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v_a_2993_);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_2993_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_a_2993_);
v_a_3024_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3015_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_traceMsgs_2995_);
lean_dec(v_macroScope_2994_);
lean_dec(v_a_2993_);
v_a_3035_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2998_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2998_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
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
lean_object* v_a_3043_; 
v_a_3043_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_2991_, 2);
if (lean_obj_tag(v_a_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_a_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v_a_3044_ = lean_ctor_get(v_a_3043_, 0);
lean_inc(v_a_3044_);
v_a_3045_ = lean_ctor_get(v_a_3043_, 1);
lean_inc_ref(v_a_3045_);
lean_dec_ref_known(v_a_3043_, 2);
v___x_3046_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___closed__0));
v___x_3047_ = lean_string_dec_eq(v_a_3045_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3045_);
v___x_3049_ = l_Lean_MessageData_ofFormat(v___x_3048_);
v___x_3050_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_a_3044_, v___x_3049_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v_a_3044_);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; 
lean_dec_ref(v_a_3045_);
v___x_3051_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_a_3044_);
return v___x_3051_;
}
}
else
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg___boxed(lean_object* v_x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object* v_pre_3062_, lean_object* v_binders_3063_, lean_object* v_type_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___y_3073_; lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_ref(v_pre_3062_);
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3077_, 0, v_type_3064_);
lean_closure_set(v___f_3077_, 1, v_pre_3062_);
v___x_3078_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___boxed), 10, 3);
lean_closure_set(v___x_3078_, 0, lean_box(0));
lean_closure_set(v___x_3078_, 1, v_binders_3063_);
lean_closure_set(v___x_3078_, 2, v___f_3077_);
v___x_3079_ = l_Lean_Elab_Term_withAutoBoundImplicit___redArg(v___x_3078_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_dec_ref(v_pre_3062_);
v___y_3073_ = v___x_3079_;
goto v___jp_3072_;
}
else
{
lean_object* v_a_3080_; uint8_t v___y_3082_; uint8_t v___x_3086_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
v___x_3086_ = l_Lean_Exception_isInterrupt(v_a_3080_);
if (v___x_3086_ == 0)
{
uint8_t v___x_3087_; 
v___x_3087_ = l_Lean_Exception_isRuntime(v_a_3080_);
v___y_3082_ = v___x_3087_;
goto v___jp_3081_;
}
else
{
lean_dec(v_a_3080_);
v___y_3082_ = v___x_3086_;
goto v___jp_3081_;
}
v___jp_3081_:
{
if (v___y_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec_ref_known(v___x_3079_, 1);
v___x_3083_ = lean_box(0);
v___x_3084_ = l_Lean_Name_str___override(v___x_3083_, v_pre_3062_);
v___x_3085_ = l_Lean_Core_mkFreshUserName(v___x_3084_, v_a_3069_, v_a_3070_);
v___y_3073_ = v___x_3085_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v_pre_3062_);
v___y_3073_ = v___x_3079_;
goto v___jp_3072_;
}
}
}
v___jp_3072_:
{
if (lean_obj_tag(v___y_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_a_3074_ = lean_ctor_get(v___y_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___y_3073_, 1);
v___x_3075_ = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName___boxed), 3, 1);
lean_closure_set(v___x_3075_, 0, v_a_3074_);
v___x_3076_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v___x_3075_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
return v___x_3076_;
}
else
{
return v___y_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27___boxed(lean_object* v_pre_3088_, lean_object* v_binders_3089_, lean_object* v_type_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v_pre_3088_, v_binders_3089_, v_type_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(lean_object* v_00_u03b1_3099_, lean_object* v_x_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___redArg(v_x_3100_, v___y_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__2(v_00_u03b1_3104_, v_x_3105_, v___y_3106_, v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec_ref(v_x_3105_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(lean_object* v_00_u03b1_3109_, lean_object* v_ref_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___redArg(v_ref_3110_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3119_, lean_object* v_ref_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__7(v_00_u03b1_3119_, v_ref_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(lean_object* v_00_u03b1_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___redArg();
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__8(v_00_u03b1_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(lean_object* v_00_u03b1_3147_, lean_object* v_x_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___redArg(v_x_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1(v_00_u03b1_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(lean_object* v_cls_3167_, lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___redArg(v_cls_3167_, v_msg_3168_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1___boxed(lean_object* v_cls_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__1(v_cls_3177_, v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(lean_object* v_as_3187_, lean_object* v_as_x27_3188_, lean_object* v_b_3189_, lean_object* v_a_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___redArg(v_as_x27_3188_, v_b_3189_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4___boxed(lean_object* v_as_3199_, lean_object* v_as_x27_3200_, lean_object* v_b_3201_, lean_object* v_a_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__4(v_as_3199_, v_as_x27_3200_, v_b_3201_, v_a_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v_as_x27_3200_);
lean_dec(v_as_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(lean_object* v_00_u03b1_3211_, lean_object* v_ref_3212_, lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___redArg(v_ref_3212_, v_msg_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_ref_3223_, lean_object* v_msg_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6(v_00_u03b1_3222_, v_ref_3223_, v_msg_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v_ref_3223_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3233_, lean_object* v_m_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___redArg(v_m_3234_, v_a_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3237_, lean_object* v_m_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6(v_00_u03b2_3237_, v_m_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_m_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(lean_object* v_00_u03b1_3241_, lean_object* v_msg_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___redArg(v_msg_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b1_3251_, lean_object* v_msg_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10(v_00_u03b1_3251_, v_msg_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
return v_res_3260_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
uint8_t v___x_3264_; 
v___x_3264_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___redArg(v_x_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7(v_00_u03b2_3265_, v_x_3266_, v_x_3267_);
lean_dec_ref(v_x_3267_);
lean_dec_ref(v_x_3266_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_3270_, lean_object* v_a_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___redArg(v_a_3271_, v_x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3274_, lean_object* v_a_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_3274_, v_a_3275_, v_x_3276_);
lean_dec(v_x_3276_);
lean_dec(v_a_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(lean_object* v_msgData_3278_, lean_object* v_macroStack_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___redArg(v_msgData_3278_, v_macroStack_3279_, v___y_3284_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15___boxed(lean_object* v_msgData_3288_, lean_object* v_macroStack_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__6_spec__10_spec__15(v_msgData_3288_, v_macroStack_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v_res_3297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, size_t v_x_3300_, lean_object* v_x_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___redArg(v_x_3299_, v_x_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
size_t v_x_15683__boxed_3307_; uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_x_15683__boxed_3307_ = lean_unbox_usize(v_x_3305_);
lean_dec(v_x_3305_);
v_res_3308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3303_, v_x_3304_, v_x_15683__boxed_3307_, v_x_3306_);
lean_dec_ref(v_x_3306_);
lean_dec_ref(v_x_3304_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* v_00_u03b2_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_heq_3313_, lean_object* v_i_3314_, lean_object* v_k_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(v_keys_3311_, v_i_3314_, v_k_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_keys_3318_, lean_object* v_vals_3319_, lean_object* v_heq_3320_, lean_object* v_i_3321_, lean_object* v_k_3322_){
_start:
{
uint8_t v_res_3323_; lean_object* v_r_3324_; 
v_res_3323_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27_spec__1_spec__3_spec__4_spec__7_spec__11_spec__15(v_00_u03b2_3317_, v_keys_3318_, v_vals_3319_, v_heq_3320_, v_i_3321_, v_k_3322_);
lean_dec_ref(v_k_3322_);
lean_dec_ref(v_vals_3319_);
lean_dec_ref(v_keys_3318_);
v_r_3324_ = lean_box(v_res_3323_);
return v_r_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0(lean_object* v_binders_3326_, lean_object* v_type_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Command_mkInstanceName___lam__0___closed__0));
v___x_3337_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_3336_, v_binders_3326_, v_type_3327_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__0___boxed(lean_object* v_binders_3338_, lean_object* v_type_3339_, lean_object* v_x_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Elab_Command_mkInstanceName___lam__0(v_binders_3338_, v_type_3339_, v_x_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v_x_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1(lean_object* v_a_3349_, lean_object* v_val_3350_, lean_object* v_a_x3f_3351_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_st_ref_swap(v_a_3349_, v_val_3350_);
lean_dec(v___x_3354_);
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___lam__1___boxed(lean_object* v_a_3356_, lean_object* v_val_3357_, lean_object* v_a_x3f_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3356_, v_val_3357_, v_a_x3f_3358_);
lean_dec(v_a_x3f_3358_);
lean_dec(v_a_3356_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object* v_binders_3361_, lean_object* v_type_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v_r_3368_; 
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkInstanceName___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3366_, 0, v_binders_3361_);
lean_closure_set(v___f_3366_, 1, v_type_3362_);
v___x_3367_ = lean_st_ref_get(v_a_3364_);
v_r_3368_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3366_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v_r_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3385_; 
v_a_3369_ = lean_ctor_get(v_r_3368_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_r_3368_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3371_ = v_r_3368_;
v_isShared_3372_ = v_isSharedCheck_3385_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v_r_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3385_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
lean_inc(v_a_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v___x_3375_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3364_, v___x_3367_, v___x_3374_);
lean_dec_ref(v___x_3374_);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v___x_3375_, 0);
lean_dec(v_unused_3383_);
v___x_3377_ = v___x_3375_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_dec(v___x_3375_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v_a_3369_);
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3369_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
v_a_3386_ = lean_ctor_get(v_r_3368_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v_r_3368_, 1);
v___x_3387_ = lean_box(0);
v___x_3388_ = l_Lean_Elab_Command_mkInstanceName___lam__1(v_a_3364_, v___x_3367_, v___x_3387_);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v___x_3388_, 0);
lean_dec(v_unused_3396_);
v___x_3390_ = v___x_3388_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v___x_3388_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 1);
lean_ctor_set(v___x_3390_, 0, v_a_3386_);
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3386_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkInstanceName___boxed(lean_object* v_binders_3397_, lean_object* v_type_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_Command_mkInstanceName(v_binders_3397_, v_type_3398_, v_a_3399_, v_a_3400_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
return v_res_3402_;
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
