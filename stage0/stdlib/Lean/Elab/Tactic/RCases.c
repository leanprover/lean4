// Lean compiler output
// Module: Lean.Elab.Tactic.RCases
// Imports: public import Lean.Elab.Tactic.ElabTerm import Lean.Elab.Tactic.Induction import Lean.Meta.Tactic.Replace import Init.Omega import Lean.Elab.Binders import Lean.Meta.Tactic.Generalize
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
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTargetView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_MVarId_generalize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_append(lean_object*, lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__0_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__0_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__0_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__1_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unusedRCasesPattern"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__1_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__1_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__0_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__1_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(241, 110, 176, 132, 250, 17, 111, 167)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__3_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "enable the 'unused rcases pattern' linter"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__3_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__3_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__4_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__3_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__4_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__4_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "RCases"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 201, 5, 192, 82, 140, 48, 247)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__0_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(147, 223, 250, 211, 237, 138, 169, 175)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__1_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(20, 239, 52, 188, 35, 247, 154, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_linter_unusedRCasesPattern;
static lean_once_cell_t l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rcasesPat"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(186, 152, 172, 228, 11, 240, 156, 168)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rcasesPatMed"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 13, 65, 195, 228, 27, 47, 149)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rcasesPatLo"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 222, 245, 138, 122, 92, 170, 214)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rintroPat"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 214, 202, 122, 59, 249, 35, 61)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.paren"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.one"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.clear"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__8_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.explicit"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__11_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.typed"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__14_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.tuple"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__17_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__19_value;
static const lean_string_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__9_value;
static const lean_string_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Elab.Tactic.RCases.RCasesPatt.alts"};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__20_value)}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_RCases_instReprRCasesPatt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt = (const lean_object*)&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__11_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Tactic `rcases` failed: `"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` is not a free variable"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__0 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__0_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__0_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` is not an inductive datatype"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.RCases"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Elab.Tactic.RCases.0.Lean.Elab.Tactic.RCases.rcasesCore"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0;
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Tactic `rcases` failed: scrutinee"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ignore"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 25, 234, 135, 235, 67, 128, 26)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 140, 213, 205, 205, 202, 106, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(176, 12, 240, 143, 52, 56, 179, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(50, 241, 13, 230, 132, 227, 26, 91)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__8_value),LEAN_SCALAR_PTR_LITERAL(201, 230, 23, 208, 164, 113, 201, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0_value;
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binder"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 86, 105, 110, 83, 1, 132, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rcases"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 76, 101, 33, 30, 11, 121, 59)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(122, 52, 29, 174, 40, 151, 224, 90)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 179, 90, 171, 127, 72, 101, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 117, 212, 174, 24, 179, 108, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__6_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 219, 0, 232, 118, 1, 211, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(1, 24, 171, 126, 91, 218, 61, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__8_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 47, 146, 235, 255, 63, 27, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRCases"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(68, 30, 19, 113, 199, 28, 14, 204)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "obtain"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 177, 143, 165, 56, 37, 104, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 140, .m_capacity = 140, .m_length = 131, .m_data = "`obtain` requires either an expected type or a value.\nusage: `obtain ⟨patt⟩\? : type (:= val)\?` or `obtain ⟨patt⟩\? (: type)\? := val`"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalObtain"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 145, 236, 142, 97, 1, 16, 15)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rintro"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__5_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__7_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 254, 242, 235, 94, 162, 254, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRIntro"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 67, 34, 189, 79, 70, 53, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__2_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__4_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn___closed__9_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_();
return v_res_62_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0(void){
_start:
{
uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = 0;
v___x_64_ = lean_box(0);
v___x_65_ = l_Lean_SourceInfo_fromRef(v___x_64_, v___x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0(lean_object* v_stx_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0, &l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0);
v___x_77_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
v___x_78_ = l_Lean_Syntax_node1(v___x_76_, v___x_77_, v_stx_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object* v_stx_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0, &l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0);
v___x_92_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_93_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_94_ = l_Lean_Syntax_node1(v___x_91_, v___x_93_, v_stx_90_);
v___x_95_ = l_Lean_Syntax_node1(v___x_91_, v___x_92_, v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Array_mkArray0___redArg();
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2, &l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__2);
v___x_106_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_107_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0, &l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0(lean_object* v_stx_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0, &l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0);
v___x_111_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_112_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3, &l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__3);
v___x_113_ = l_Lean_Syntax_node2(v___x_110_, v___x_111_, v_stx_109_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0(lean_object* v_stx_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0, &l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__0);
v___x_125_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
v___x_126_ = l_Lean_Syntax_node1(v___x_124_, v___x_125_, v_stx_123_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx(lean_object* v_x_129_){
_start:
{
switch(lean_obj_tag(v_x_129_))
{
case 0:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(0u);
return v___x_130_;
}
case 1:
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(1u);
return v___x_131_;
}
case 2:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(2u);
return v___x_132_;
}
case 3:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(3u);
return v___x_133_;
}
case 4:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(4u);
return v___x_134_;
}
case 5:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(5u);
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(6u);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx(v_x_137_);
lean_dec_ref(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(lean_object* v_t_139_, lean_object* v_k_140_){
_start:
{
switch(lean_obj_tag(v_t_139_))
{
case 0:
{
lean_object* v_ref_141_; lean_object* v_a_142_; lean_object* v___x_143_; 
v_ref_141_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_ref_141_);
v_a_142_ = lean_ctor_get(v_t_139_, 1);
lean_inc_ref(v_a_142_);
lean_dec_ref_known(v_t_139_, 2);
v___x_143_ = lean_apply_2(v_k_140_, v_ref_141_, v_a_142_);
return v___x_143_;
}
case 2:
{
lean_object* v_ref_144_; lean_object* v___x_145_; 
v_ref_144_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_ref_144_);
lean_dec_ref_known(v_t_139_, 1);
v___x_145_ = lean_apply_1(v_k_140_, v_ref_144_);
return v___x_145_;
}
case 3:
{
lean_object* v_ref_146_; lean_object* v_a_147_; lean_object* v___x_148_; 
v_ref_146_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_ref_146_);
v_a_147_ = lean_ctor_get(v_t_139_, 1);
lean_inc_ref(v_a_147_);
lean_dec_ref_known(v_t_139_, 2);
v___x_148_ = lean_apply_2(v_k_140_, v_ref_146_, v_a_147_);
return v___x_148_;
}
case 4:
{
lean_object* v_ref_149_; lean_object* v_a_150_; lean_object* v_a_151_; lean_object* v___x_152_; 
v_ref_149_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_ref_149_);
v_a_150_ = lean_ctor_get(v_t_139_, 1);
lean_inc_ref(v_a_150_);
v_a_151_ = lean_ctor_get(v_t_139_, 2);
lean_inc(v_a_151_);
lean_dec_ref_known(v_t_139_, 3);
v___x_152_ = lean_apply_3(v_k_140_, v_ref_149_, v_a_150_, v_a_151_);
return v___x_152_;
}
default: 
{
lean_object* v_ref_153_; lean_object* v_a_154_; lean_object* v___x_155_; 
v_ref_153_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_ref_153_);
v_a_154_ = lean_ctor_get(v_t_139_, 1);
lean_inc(v_a_154_);
lean_dec_ref(v_t_139_);
v___x_155_ = lean_apply_2(v_k_140_, v_ref_153_, v_a_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim(lean_object* v_motive__1_156_, lean_object* v_ctorIdx_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_k_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_158_, v_k_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___boxed(lean_object* v_motive__1_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim(v_motive__1_162_, v_ctorIdx_163_, v_t_164_, v_h_165_, v_k_166_);
lean_dec(v_ctorIdx_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim___redArg(lean_object* v_t_168_, lean_object* v_paren_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_168_, v_paren_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim(lean_object* v_motive__1_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_paren_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_172_, v_paren_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim___redArg(lean_object* v_t_176_, lean_object* v_one_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_176_, v_one_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim(lean_object* v_motive__1_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_one_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_180_, v_one_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim___redArg(lean_object* v_t_184_, lean_object* v_clear_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_184_, v_clear_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim(lean_object* v_motive__1_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_clear_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_188_, v_clear_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim___redArg(lean_object* v_t_192_, lean_object* v_explicit_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_192_, v_explicit_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim(lean_object* v_motive__1_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_explicit_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_196_, v_explicit_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim___redArg(lean_object* v_t_200_, lean_object* v_typed_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_200_, v_typed_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim(lean_object* v_motive__1_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_typed_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_204_, v_typed_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim___redArg(lean_object* v_t_208_, lean_object* v_tuple_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_208_, v_tuple_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim(lean_object* v_motive__1_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_tuple_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_212_, v_tuple_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim___redArg(lean_object* v_t_216_, lean_object* v_alts_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_216_, v_alts_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim(lean_object* v_motive__1_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_alts_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_220_, v_alts_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(2u);
v___x_231_ = lean_nat_to_int(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_dec(v_x_273_);
return v_x_274_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_288_; 
v_head_276_ = lean_ctor_get(v_x_275_, 0);
v_tail_277_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_288_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_head_276_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
lean_inc(v_x_273_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 5);
lean_ctor_set(v___x_279_, 1, v_x_273_);
lean_ctor_set(v___x_279_, 0, v_x_274_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_x_273_);
v___x_282_ = v_reuseFailAlloc_287_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_head_276_, v___x_283_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v_x_274_ = v___x_285_;
v_x_275_ = v_tail_277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_dec(v_x_289_);
return v_x_290_;
}
else
{
lean_object* v_head_292_; lean_object* v_tail_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_304_; 
v_head_292_ = lean_ctor_get(v_x_291_, 0);
v_tail_293_ = lean_ctor_get(v_x_291_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_304_ == 0)
{
v___x_295_ = v_x_291_;
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_tail_293_);
lean_inc(v_head_292_);
lean_dec(v_x_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
lean_inc(v_x_289_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 5);
lean_ctor_set(v___x_295_, 1, v_x_289_);
lean_ctor_set(v___x_295_, 0, v_x_290_);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_x_290_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_x_289_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_head_292_, v___x_299_);
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1_spec__3(v_x_289_, v___x_301_, v_tail_293_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_307_; 
lean_dec(v_x_306_);
v___x_307_ = lean_box(0);
return v___x_307_;
}
else
{
lean_object* v_tail_308_; 
v_tail_308_ = lean_ctor_get(v_x_305_, 1);
if (lean_obj_tag(v_tail_308_) == 0)
{
lean_object* v_head_309_; lean_object* v___x_310_; 
lean_dec(v_x_306_);
v_head_309_ = lean_ctor_get(v_x_305_, 0);
lean_inc(v_head_309_);
lean_dec_ref_known(v_x_305_, 2);
v___x_310_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(v_head_309_);
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc(v_tail_308_);
v_head_311_ = lean_ctor_get(v_x_305_, 0);
lean_inc(v_head_311_);
lean_dec_ref_known(v_x_305_, 2);
v___x_312_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(v_head_311_);
v___x_313_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1(v_x_306_, v___x_312_, v_tail_308_);
return v___x_313_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2));
v___x_316_ = lean_string_length(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(lean_object* v_a_324_){
_start:
{
if (lean_obj_tag(v_a_324_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__1));
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; 
v___x_326_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__5));
v___x_327_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0(v_a_324_, v___x_326_);
v___x_328_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8);
v___x_329_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__9));
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_327_);
v___x_331_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__10));
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_328_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = 0;
v___x_335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(lean_object* v_x_342_, lean_object* v_prec_343_){
_start:
{
switch(lean_obj_tag(v_x_342_))
{
case 0:
{
lean_object* v_ref_344_; lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_368_; 
v_ref_344_ = lean_ctor_get(v_x_342_, 0);
v_a_345_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_368_ == 0)
{
v___x_347_ = v_x_342_;
v_isShared_348_ = v_isSharedCheck_368_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_inc(v_ref_344_);
lean_dec(v_x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_368_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___y_351_; uint8_t v___x_365_; 
v___x_349_ = lean_unsigned_to_nat(1024u);
v___x_365_ = lean_nat_dec_le(v___x_349_, v_prec_343_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_351_ = v___x_366_;
goto v___jp_350_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_351_ = v___x_367_;
goto v___jp_350_;
}
v___jp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_352_ = lean_box(1);
v___x_353_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__2));
v___x_354_ = l_Lean_Syntax_instRepr_repr(v_ref_344_, v___x_349_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 5);
lean_ctor_set(v___x_347_, 1, v___x_354_);
lean_ctor_set(v___x_347_, 0, v___x_353_);
v___x_356_ = v___x_347_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_364_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_352_);
v___x_358_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_345_, v___x_349_);
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
lean_inc(v___y_351_);
v___x_360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_360_, 0, v___y_351_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = 0;
v___x_362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*1, v___x_361_);
v___x_363_ = l_Repr_addAppParen(v___x_362_, v_prec_343_);
return v___x_363_;
}
}
}
}
case 1:
{
lean_object* v_ref_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_394_; 
v_ref_369_ = lean_ctor_get(v_x_342_, 0);
v_a_370_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_394_ == 0)
{
v___x_372_ = v_x_342_;
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_inc(v_ref_369_);
lean_dec(v_x_342_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1024u);
v___x_391_ = lean_nat_dec_le(v___x_390_, v_prec_343_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_375_ = v___x_392_;
goto v___jp_374_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_375_ = v___x_393_;
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_376_ = lean_box(1);
v___x_377_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__7));
v___x_378_ = lean_unsigned_to_nat(1024u);
v___x_379_ = l_Lean_Syntax_instRepr_repr(v_ref_369_, v___x_378_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 5);
lean_ctor_set(v___x_372_, 1, v___x_379_);
lean_ctor_set(v___x_372_, 0, v___x_377_);
v___x_381_ = v___x_372_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_389_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_376_);
v___x_383_ = l_Lean_Name_reprPrec(v_a_370_, v___x_378_);
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
lean_inc(v___y_375_);
v___x_385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_385_, 0, v___y_375_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = 0;
v___x_387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_386_);
v___x_388_ = l_Repr_addAppParen(v___x_387_, v_prec_343_);
return v___x_388_;
}
}
}
}
case 2:
{
lean_object* v_ref_395_; lean_object* v___y_397_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_ref_395_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_ref_395_);
lean_dec_ref_known(v_x_342_, 1);
v___x_406_ = lean_unsigned_to_nat(1024u);
v___x_407_ = lean_nat_dec_le(v___x_406_, v_prec_343_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_397_ = v___x_408_;
goto v___jp_396_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_397_ = v___x_409_;
goto v___jp_396_;
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__10));
v___x_399_ = lean_unsigned_to_nat(1024u);
v___x_400_ = l_Lean_Syntax_instRepr_repr(v_ref_395_, v___x_399_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_398_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_inc(v___y_397_);
v___x_402_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_402_, 0, v___y_397_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = 0;
v___x_404_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1, v___x_403_);
v___x_405_ = l_Repr_addAppParen(v___x_404_, v_prec_343_);
return v___x_405_;
}
}
case 3:
{
lean_object* v_ref_410_; lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_434_; 
v_ref_410_ = lean_ctor_get(v_x_342_, 0);
v_a_411_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_434_ == 0)
{
v___x_413_ = v_x_342_;
v_isShared_414_ = v_isSharedCheck_434_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_inc(v_ref_410_);
lean_dec(v_x_342_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_434_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___y_417_; uint8_t v___x_431_; 
v___x_415_ = lean_unsigned_to_nat(1024u);
v___x_431_ = lean_nat_dec_le(v___x_415_, v_prec_343_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_417_ = v___x_432_;
goto v___jp_416_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_417_ = v___x_433_;
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_418_ = lean_box(1);
v___x_419_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__13));
v___x_420_ = l_Lean_Syntax_instRepr_repr(v_ref_410_, v___x_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 5);
lean_ctor_set(v___x_413_, 1, v___x_420_);
lean_ctor_set(v___x_413_, 0, v___x_419_);
v___x_422_ = v___x_413_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_430_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_418_);
v___x_424_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_411_, v___x_415_);
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_inc(v___y_417_);
v___x_426_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_426_, 0, v___y_417_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = 0;
v___x_428_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_427_);
v___x_429_ = l_Repr_addAppParen(v___x_428_, v_prec_343_);
return v___x_429_;
}
}
}
}
case 4:
{
lean_object* v_ref_435_; lean_object* v_a_436_; lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___y_440_; uint8_t v___x_455_; 
v_ref_435_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_ref_435_);
v_a_436_ = lean_ctor_get(v_x_342_, 1);
lean_inc_ref(v_a_436_);
v_a_437_ = lean_ctor_get(v_x_342_, 2);
lean_inc(v_a_437_);
lean_dec_ref_known(v_x_342_, 3);
v___x_438_ = lean_unsigned_to_nat(1024u);
v___x_455_ = lean_nat_dec_le(v___x_438_, v_prec_343_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_440_ = v___x_456_;
goto v___jp_439_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_440_ = v___x_457_;
goto v___jp_439_;
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_441_ = lean_box(1);
v___x_442_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__16));
v___x_443_ = l_Lean_Syntax_instRepr_repr(v_ref_435_, v___x_438_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_441_);
v___x_446_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_436_, v___x_438_);
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_441_);
v___x_449_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_a_437_);
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_inc(v___y_440_);
v___x_451_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_440_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = 0;
v___x_453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___x_452_);
v___x_454_ = l_Repr_addAppParen(v___x_453_, v_prec_343_);
return v___x_454_;
}
}
case 5:
{
lean_object* v_ref_458_; lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_483_; 
v_ref_458_ = lean_ctor_get(v_x_342_, 0);
v_a_459_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_483_ == 0)
{
v___x_461_ = v_x_342_;
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_inc(v_ref_458_);
lean_dec(v_x_342_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___y_464_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1024u);
v___x_480_ = lean_nat_dec_le(v___x_479_, v_prec_343_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_464_ = v___x_481_;
goto v___jp_463_;
}
else
{
lean_object* v___x_482_; 
v___x_482_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_464_ = v___x_482_;
goto v___jp_463_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_465_ = lean_box(1);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__19));
v___x_467_ = lean_unsigned_to_nat(1024u);
v___x_468_ = l_Lean_Syntax_instRepr_repr(v_ref_458_, v___x_467_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_468_);
lean_ctor_set(v___x_461_, 0, v___x_466_);
v___x_470_ = v___x_461_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_478_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_465_);
v___x_472_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_459_);
v___x_473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_inc(v___y_464_);
v___x_474_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_464_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = 0;
v___x_476_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*1, v___x_475_);
v___x_477_ = l_Repr_addAppParen(v___x_476_, v_prec_343_);
return v___x_477_;
}
}
}
}
default: 
{
lean_object* v_ref_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_509_; 
v_ref_484_ = lean_ctor_get(v_x_342_, 0);
v_a_485_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_509_ == 0)
{
v___x_487_ = v_x_342_;
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_inc(v_ref_484_);
lean_dec(v_x_342_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___y_490_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1024u);
v___x_506_ = lean_nat_dec_le(v___x_505_, v_prec_343_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_490_ = v___x_507_;
goto v___jp_489_;
}
else
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_490_ = v___x_508_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_491_ = lean_box(1);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__22));
v___x_493_ = lean_unsigned_to_nat(1024u);
v___x_494_ = l_Lean_Syntax_instRepr_repr(v_ref_484_, v___x_493_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 5);
lean_ctor_set(v___x_487_, 1, v___x_494_);
lean_ctor_set(v___x_487_, 0, v___x_492_);
v___x_496_ = v___x_487_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_504_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_491_);
v___x_498_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_485_);
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_inc(v___y_490_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___y_490_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
v___x_503_ = l_Repr_addAppParen(v___x_502_, v_prec_343_);
return v___x_503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(lean_object* v___y_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v___y_510_, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___boxed(lean_object* v_x_513_, lean_object* v_prec_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_x_513_, v_prec_514_);
lean_dec(v_prec_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__1(lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_nat_to_int(v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0(lean_object* v_a_518_, lean_object* v_n_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___boxed(lean_object* v_a_521_, lean_object* v_n_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0(v_a_521_, v_n_522_);
lean_dec(v_n_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(lean_object* v_x_534_){
_start:
{
switch(lean_obj_tag(v_x_534_))
{
case 1:
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v_x_534_, 1);
if (lean_obj_tag(v_a_535_) == 1)
{
lean_object* v_pre_536_; 
v_pre_536_ = lean_ctor_get(v_a_535_, 0);
if (lean_obj_tag(v_pre_536_) == 0)
{
lean_object* v_str_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_str_537_ = lean_ctor_get(v_a_535_, 1);
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0));
v___x_539_ = lean_string_dec_eq(v_str_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_541_ = lean_string_dec_eq(v_str_537_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_inc_ref(v_a_535_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_a_535_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(0);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; 
lean_inc_ref(v_a_535_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_a_535_);
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; 
lean_inc(v_a_535_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v_a_535_);
return v___x_546_;
}
}
case 0:
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v_x_534_, 1);
v_x_534_ = v_a_547_;
goto _start;
}
case 4:
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v_x_534_, 1);
v_x_534_ = v_a_549_;
goto _start;
}
case 6:
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v_x_534_, 1);
if (lean_obj_tag(v_a_551_) == 1)
{
lean_object* v_tail_552_; 
v_tail_552_ = lean_ctor_get(v_a_551_, 1);
if (lean_obj_tag(v_tail_552_) == 0)
{
lean_object* v_head_553_; 
v_head_553_ = lean_ctor_get(v_a_551_, 0);
v_x_534_ = v_head_553_;
goto _start;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(0);
return v___x_555_;
}
}
else
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
}
default: 
{
lean_object* v___x_557_; 
v___x_557_ = lean_box(0);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___boxed(lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_x_558_);
lean_dec_ref(v_x_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref(lean_object* v_x_560_){
_start:
{
lean_object* v_ref_561_; 
v_ref_561_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_ref_561_);
return v_ref_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref___boxed(lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref(v_x_562_);
lean_dec_ref(v_x_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(lean_object* v_x_564_){
_start:
{
switch(lean_obj_tag(v_x_564_))
{
case 0:
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v_x_564_, 1);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v_x_564_, 2);
v_x_564_ = v_a_565_;
goto _start;
}
case 3:
{
lean_object* v_a_567_; lean_object* v___x_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
v_a_567_ = lean_ctor_get(v_x_564_, 1);
lean_inc_ref(v_a_567_);
lean_dec_ref_known(v_x_564_, 2);
v___x_568_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_a_567_);
v_snd_569_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_568_, 0);
lean_dec(v_unused_579_);
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = 1;
v___x_574_ = lean_box(v___x_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_snd_569_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
case 5:
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_589_; 
v_a_580_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_x_564_, 0);
lean_dec(v_unused_590_);
v___x_582_ = v_x_564_;
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_x_564_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = 0;
v___x_585_ = lean_box(v___x_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_a_580_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
default: 
{
uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_591_ = 0;
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v_x_564_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_box(v___x_591_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(lean_object* v_x_596_){
_start:
{
switch(lean_obj_tag(v_x_596_))
{
case 0:
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v_x_596_, 1);
lean_inc_ref(v_a_597_);
lean_dec_ref_known(v_x_596_, 2);
v_x_596_ = v_a_597_;
goto _start;
}
case 6:
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v_x_596_, 1);
lean_inc(v_a_599_);
lean_dec_ref_known(v_x_596_, 2);
return v_a_599_;
}
default: 
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_x_596_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(lean_object* v_ref_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_dec(v_ref_602_);
return v_x_603_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_606_; 
v_val_605_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_val_605_);
v___x_606_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_606_, 0, v_ref_602_);
lean_ctor_set(v___x_606_, 1, v_x_603_);
lean_ctor_set(v___x_606_, 2, v_val_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f___boxed(lean_object* v_ref_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_607_, v_x_608_, v_x_609_);
lean_dec(v_x_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_x27(lean_object* v_x_611_){
_start:
{
lean_object* v_ps_613_; 
if (lean_obj_tag(v_x_611_) == 1)
{
lean_object* v_tail_640_; 
v_tail_640_ = lean_ctor_get(v_x_611_, 1);
if (lean_obj_tag(v_tail_640_) == 0)
{
lean_object* v_head_641_; 
v_head_641_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_head_641_);
lean_dec_ref_known(v_x_611_, 2);
return v_head_641_;
}
else
{
v_ps_613_ = v_x_611_;
goto v___jp_612_;
}
}
else
{
v_ps_613_ = v_x_611_;
goto v___jp_612_;
}
v___jp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = l_List_head_x3f___redArg(v_ps_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_ps_613_);
return v___x_616_;
}
else
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___x_614_, 1);
switch(lean_obj_tag(v_val_617_))
{
case 2:
{
lean_object* v_ref_618_; lean_object* v___x_619_; 
v_ref_618_ = lean_ctor_get(v_val_617_, 0);
lean_inc(v_ref_618_);
lean_dec_ref_known(v_val_617_, 1);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v_ref_618_);
lean_ctor_set(v___x_619_, 1, v_ps_613_);
return v___x_619_;
}
case 4:
{
lean_object* v_ref_620_; lean_object* v___x_621_; 
v_ref_620_ = lean_ctor_get(v_val_617_, 0);
lean_inc(v_ref_620_);
lean_dec_ref_known(v_val_617_, 3);
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v_ref_620_);
lean_ctor_set(v___x_621_, 1, v_ps_613_);
return v___x_621_;
}
case 5:
{
lean_object* v_ref_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_ref_622_ = lean_ctor_get(v_val_617_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_val_617_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_val_617_, 1);
lean_dec(v_unused_630_);
v___x_624_ = v_val_617_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_ref_622_);
lean_dec(v_val_617_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_ps_613_);
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_ref_622_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_ps_613_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
default: 
{
lean_object* v_ref_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_ref_631_ = lean_ctor_get(v_val_617_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_val_617_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_val_617_, 1);
lean_dec(v_unused_639_);
v___x_633_ = v_val_617_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_ref_631_);
lean_dec(v_val_617_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 5);
lean_ctor_set(v___x_633_, 1, v_ps_613_);
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_ref_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_ps_613_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(lean_object* v_ref_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 1)
{
lean_object* v_tail_644_; 
v_tail_644_ = lean_ctor_get(v_x_643_, 1);
if (lean_obj_tag(v_tail_644_) == 0)
{
lean_object* v_head_645_; 
lean_dec(v_ref_642_);
v_head_645_ = lean_ctor_get(v_x_643_, 0);
lean_inc(v_head_645_);
lean_dec_ref_known(v_x_643_, 2);
return v_head_645_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_646_, 0, v_ref_642_);
lean_ctor_set(v___x_646_, 1, v_x_643_);
return v___x_646_;
}
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_647_, 0, v_ref_642_);
lean_ctor_set(v___x_647_, 1, v_x_643_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
return v_x_648_;
}
else
{
lean_object* v_head_649_; lean_object* v_tail_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_670_; 
v_head_649_ = lean_ctor_get(v_x_648_, 0);
v_tail_650_ = lean_ctor_get(v_x_648_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_670_ == 0)
{
v___x_652_ = v_x_648_;
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_tail_650_);
lean_inc(v_head_649_);
lean_dec(v_x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
if (lean_obj_tag(v_head_649_) == 5)
{
lean_object* v_a_659_; 
v_a_659_ = lean_ctor_get(v_head_649_, 1);
if (lean_obj_tag(v_a_659_) == 0)
{
if (lean_obj_tag(v_tail_650_) == 0)
{
lean_object* v_ref_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
lean_del_object(v___x_652_);
v_ref_660_ = lean_ctor_get(v_head_649_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_head_649_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_head_649_, 1);
lean_dec(v_unused_669_);
v___x_662_ = v_head_649_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_ref_660_);
lean_dec(v_head_649_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v_tail_650_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_ref_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_tail_650_);
v___x_665_ = v_reuseFailAlloc_667_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_tail_650_);
return v___x_666_;
}
}
}
else
{
goto v___jp_654_;
}
}
else
{
if (lean_obj_tag(v_tail_650_) == 0)
{
lean_inc(v_a_659_);
lean_dec_ref_known(v_head_649_, 2);
lean_del_object(v___x_652_);
return v_a_659_;
}
else
{
goto v___jp_654_;
}
}
}
else
{
goto v___jp_654_;
}
v___jp_654_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(v_tail_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_head_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081(lean_object* v_x_671_){
_start:
{
lean_object* v___y_673_; lean_object* v___y_674_; 
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
return v___x_677_;
}
else
{
lean_object* v_head_678_; lean_object* v_tail_679_; lean_object* v___x_680_; lean_object* v_ps_682_; 
v_head_678_ = lean_ctor_get(v_x_671_, 0);
v_tail_679_ = lean_ctor_get(v_x_671_, 1);
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited));
if (lean_obj_tag(v_head_678_) == 1)
{
if (lean_obj_tag(v_tail_679_) == 0)
{
lean_inc_ref(v_head_678_);
lean_dec_ref_known(v_x_671_, 2);
return v_head_678_;
}
else
{
v_ps_682_ = v_x_671_;
goto v___jp_681_;
}
}
else
{
v_ps_682_ = v_x_671_;
goto v___jp_681_;
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v_ref_684_; 
v___x_683_ = l_List_head_x21___redArg(v___x_680_, v_ps_682_);
v_ref_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_ref_684_);
lean_dec(v___x_683_);
v___y_673_ = v_ps_682_;
v___y_674_ = v_ref_684_;
goto v___jp_672_;
}
}
v___jp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(v___y_673_);
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___y_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_box(0);
return v___x_686_;
}
else
{
lean_object* v_head_687_; lean_object* v_tail_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_701_; 
v_head_687_ = lean_ctor_get(v_x_685_, 0);
v_tail_688_ = lean_ctor_get(v_x_685_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_685_);
if (v_isSharedCheck_701_ == 0)
{
v___x_690_ = v_x_685_;
v_isShared_691_ = v_isSharedCheck_701_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_tail_688_);
lean_inc(v_head_687_);
lean_dec(v_x_685_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_701_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_head_687_) == 1)
{
lean_object* v_head_698_; 
v_head_698_ = lean_ctor_get(v_head_687_, 0);
if (lean_obj_tag(v_head_698_) == 6)
{
lean_object* v_tail_699_; 
v_tail_699_ = lean_ctor_get(v_head_687_, 1);
if (lean_obj_tag(v_tail_699_) == 0)
{
if (lean_obj_tag(v_tail_688_) == 0)
{
lean_object* v_a_700_; 
lean_inc_ref(v_head_698_);
lean_dec_ref_known(v_head_687_, 2);
lean_del_object(v___x_690_);
v_a_700_ = lean_ctor_get(v_head_698_, 1);
lean_inc(v_a_700_);
lean_dec_ref_known(v_head_698_, 2);
return v_a_700_;
}
else
{
goto v___jp_692_;
}
}
else
{
goto v___jp_692_;
}
}
else
{
goto v___jp_692_;
}
}
else
{
goto v___jp_692_;
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081(v_head_687_);
v___x_694_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(v_tail_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_694_);
lean_ctor_set(v___x_690_, 0, v___x_693_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081(lean_object* v_ref_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_ps_705_; 
if (lean_obj_tag(v_x_703_) == 1)
{
lean_object* v_head_708_; 
v_head_708_ = lean_ctor_get(v_x_703_, 0);
if (lean_obj_tag(v_head_708_) == 0)
{
lean_object* v_tail_709_; 
v_tail_709_ = lean_ctor_get(v_x_703_, 1);
if (lean_obj_tag(v_tail_709_) == 0)
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
lean_inc(v_head_708_);
lean_dec(v_ref_702_);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; 
v_unused_718_ = lean_ctor_get(v_x_703_, 1);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_x_703_, 0);
lean_dec(v_unused_719_);
v___x_711_ = v_x_703_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_dec(v_x_703_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 5);
lean_ctor_set(v___x_711_, 1, v_head_708_);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_head_708_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
v_ps_705_ = v_x_703_;
goto v___jp_704_;
}
}
else
{
lean_object* v_head_720_; 
v_head_720_ = lean_ctor_get(v_head_708_, 0);
lean_inc(v_head_720_);
if (lean_obj_tag(v_head_720_) == 6)
{
lean_object* v_tail_721_; 
v_tail_721_ = lean_ctor_get(v_head_708_, 1);
if (lean_obj_tag(v_tail_721_) == 0)
{
lean_object* v_tail_722_; 
v_tail_722_ = lean_ctor_get(v_x_703_, 1);
if (lean_obj_tag(v_tail_722_) == 0)
{
lean_object* v_ref_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref_known(v_x_703_, 2);
lean_dec(v_ref_702_);
v_ref_723_ = lean_ctor_get(v_head_720_, 0);
v_a_724_ = lean_ctor_get(v_head_720_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_head_720_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v_head_720_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_inc(v_ref_723_);
lean_dec(v_head_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 5);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_ref_723_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_dec_ref_known(v_head_720_, 2);
v_ps_705_ = v_x_703_;
goto v___jp_704_;
}
}
else
{
lean_dec_ref_known(v_head_720_, 2);
v_ps_705_ = v_x_703_;
goto v___jp_704_;
}
}
else
{
lean_dec(v_head_720_);
v_ps_705_ = v_x_703_;
goto v___jp_704_;
}
}
}
else
{
v_ps_705_ = v_x_703_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(v_ps_705_);
v___x_707_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_ref_702_, v___x_706_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(lean_object* v_tgt_732_, lean_object* v_p_733_, lean_object* v_m_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_lt(v_tgt_732_, v_p_733_);
if (v___x_735_ == 0)
{
return v_m_734_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_MessageData_paren(v_m_734_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove___boxed(lean_object* v_tgt_737_, lean_object* v_p_738_, lean_object* v_m_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v_tgt_737_, v_p_738_, v_m_739_);
lean_dec(v_p_738_);
lean_dec(v_tgt_737_);
return v_res_740_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__1));
v___x_745_ = l_Lean_MessageData_ofFormat(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__3));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__5));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_box(1);
v___x_754_ = l_Lean_MessageData_ofFormat(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4));
v___x_756_ = l_Lean_MessageData_ofFormat(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
v___x_758_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__1(lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
if (lean_obj_tag(v_a_761_) == 0)
{
lean_object* v___x_763_; 
v___x_763_ = l_List_reverse___redArg(v_a_762_);
return v___x_763_;
}
else
{
lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v_head_764_ = lean_ctor_get(v_a_761_, 0);
v_tail_765_ = lean_ctor_get(v_a_761_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_761_);
if (v_isSharedCheck_775_ == 0)
{
v___x_767_ = v_a_761_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_inc(v_head_764_);
lean_dec(v_a_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = lean_unsigned_to_nat(2u);
v___x_770_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_769_, v_head_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_a_762_);
lean_ctor_set(v___x_767_, 0, v___x_770_);
v___x_772_ = v___x_767_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_a_762_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_a_761_ = v_tail_765_;
v_a_762_ = v___x_772_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__13));
v___x_780_ = l_Lean_MessageData_ofFormat(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
switch(lean_obj_tag(v_a_782_))
{
case 0:
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v_a_782_, 1);
lean_inc_ref(v_a_783_);
lean_dec_ref_known(v_a_782_, 2);
v_a_782_ = v_a_783_;
goto _start;
}
case 1:
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v_a_782_, 1);
lean_inc(v_a_785_);
lean_dec_ref_known(v_a_782_, 2);
v___x_786_ = l_Lean_MessageData_ofName(v_a_785_);
return v___x_786_;
}
case 2:
{
lean_object* v___x_787_; 
lean_dec_ref_known(v_a_782_, 1);
v___x_787_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2);
return v___x_787_;
}
case 3:
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
v_a_788_ = lean_ctor_get(v_a_782_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_a_782_, 0);
lean_dec(v_unused_799_);
v___x_790_ = v_a_782_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v_a_782_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_792_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4);
v___x_793_ = lean_unsigned_to_nat(2u);
v___x_794_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_793_, v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 7);
lean_ctor_set(v___x_790_, 1, v___x_794_);
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_796_ = v___x_790_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
case 4:
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_a_800_ = lean_ctor_get(v_a_782_, 1);
lean_inc_ref(v_a_800_);
v_a_801_ = lean_ctor_get(v_a_782_, 2);
lean_inc(v_a_801_);
lean_dec_ref_known(v_a_782_, 3);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_803_, v_a_800_);
v___x_805_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_MessageData_ofSyntax(v_a_801_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v___x_802_, v_a_781_, v___x_808_);
return v___x_809_;
}
case 5:
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_a_810_ = lean_ctor_get(v_a_782_, 1);
lean_inc(v_a_810_);
lean_dec_ref_known(v_a_782_, 2);
v___x_811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__7));
v___x_812_ = lean_box(0);
v___x_813_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__0(v_a_810_, v___x_812_);
v___x_814_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10);
v___x_815_ = l_Lean_MessageData_joinSep(v___x_813_, v___x_814_);
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__11));
v___x_817_ = l_Lean_MessageData_bracket(v___x_811_, v___x_815_, v___x_816_);
return v___x_817_;
}
default: 
{
lean_object* v_a_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_818_ = lean_ctor_get(v_a_782_, 1);
lean_inc(v_a_818_);
lean_dec_ref_known(v_a_782_, 2);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_box(0);
v___x_821_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__1(v_a_818_, v___x_820_);
v___x_822_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14);
v___x_823_ = l_Lean_MessageData_joinSep(v___x_821_, v___x_822_);
v___x_824_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v___x_819_, v_a_781_, v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__0(lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l_List_reverse___redArg(v_a_826_);
return v___x_827_;
}
else
{
lean_object* v_head_828_; lean_object* v_tail_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_839_; 
v_head_828_ = lean_ctor_get(v_a_825_, 0);
v_tail_829_ = lean_ctor_get(v_a_825_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_839_ == 0)
{
v___x_831_ = v_a_825_;
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_tail_829_);
lean_inc(v_head_828_);
lean_dec(v_a_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_833_, v_head_828_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_a_826_);
lean_ctor_set(v___x_831_, 0, v___x_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_826_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v_a_825_ = v_tail_829_;
v_a_826_ = v___x_836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___boxed(lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v_a_840_, v_a_841_);
lean_dec(v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(lean_object* v_ref_851_, lean_object* v_info_852_, uint8_t v_explicit_853_, lean_object* v_idx_854_, lean_object* v_ps_855_){
_start:
{
lean_object* v___y_857_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___x_889_; uint8_t v___x_908_; 
v___x_889_ = lean_array_get_size(v_info_852_);
v___x_908_ = lean_nat_dec_lt(v_idx_854_, v___x_889_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec(v_ps_855_);
lean_dec(v_ref_851_);
v___x_909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__1));
return v___x_909_;
}
else
{
if (v_explicit_853_ == 0)
{
lean_object* v___x_910_; uint8_t v_binderInfo_911_; uint8_t v___x_912_; uint8_t v___x_913_; 
v___x_910_ = lean_array_fget_borrowed(v_info_852_, v_idx_854_);
v_binderInfo_911_ = lean_ctor_get_uint8(v___x_910_, sizeof(void*)*1);
v___x_912_ = 0;
v___x_913_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_929_; 
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_idx_854_, v___x_914_);
v___x_916_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_851_, v_info_852_, v_explicit_853_, v___x_915_, v_ps_855_);
lean_dec(v___x_915_);
v_fst_917_ = lean_ctor_get(v___x_916_, 0);
v_snd_918_ = lean_ctor_get(v___x_916_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_929_ == 0)
{
v___x_920_ = v___x_916_;
v_isShared_921_ = v_isSharedCheck_929_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_snd_918_);
lean_inc(v_fst_917_);
lean_dec(v___x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_929_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_fst_917_);
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___x_925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_snd_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_925_);
lean_ctor_set(v___x_920_, 0, v___x_923_);
v___x_927_ = v___x_920_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
goto v___jp_890_;
}
}
else
{
goto v___jp_890_;
}
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___y_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_ps_855_);
return v___x_860_;
}
v___jp_861_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___y_865_);
lean_ctor_set(v___x_866_, 1, v___y_864_);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___y_862_);
lean_ctor_set(v___x_867_, 1, v___y_863_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
v___jp_869_:
{
lean_object* v___x_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_876_; 
v___x_873_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_851_, v_info_852_, v_explicit_853_, v___y_871_, v___y_872_);
lean_dec(v___y_871_);
v_fst_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_875_);
lean_dec_ref(v___x_873_);
v___x_876_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___y_870_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_862_ = v___y_870_;
v___y_863_ = v_snd_875_;
v___y_864_ = v_fst_874_;
v___y_865_ = v___x_877_;
goto v___jp_861_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___x_876_, 1);
v___y_862_ = v___y_870_;
v___y_863_ = v_snd_875_;
v___y_864_ = v_fst_874_;
v___y_865_ = v_val_878_;
goto v___jp_861_;
}
}
v___jp_879_:
{
if (lean_obj_tag(v_ps_855_) == 0)
{
v___y_870_ = v___y_881_;
v___y_871_ = v___y_880_;
v___y_872_ = v_ps_855_;
goto v___jp_869_;
}
else
{
lean_object* v_tail_882_; 
v_tail_882_ = lean_ctor_get(v_ps_855_, 1);
lean_inc(v_tail_882_);
lean_dec_ref_known(v_ps_855_, 2);
v___y_870_ = v___y_881_;
v___y_871_ = v___y_880_;
v___y_872_ = v_tail_882_;
goto v___jp_869_;
}
}
v___jp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___y_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
lean_inc(v___y_884_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___y_884_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
v___jp_890_:
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_add(v_idx_854_, v___x_891_);
v___x_893_ = lean_nat_dec_lt(v___x_892_, v___x_889_);
if (v___x_893_ == 0)
{
lean_dec(v___x_892_);
if (lean_obj_tag(v_ps_855_) == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_ref_851_);
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0));
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v_ps_855_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_894_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_tail_898_; 
v_tail_898_ = lean_ctor_get(v_ps_855_, 1);
if (lean_obj_tag(v_tail_898_) == 0)
{
lean_object* v_head_899_; lean_object* v___x_900_; 
lean_dec(v_ref_851_);
v_head_899_ = lean_ctor_get(v_ps_855_, 0);
v___x_900_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_head_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_857_ = v___x_901_;
goto v___jp_856_;
}
else
{
lean_object* v_val_902_; 
v_val_902_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v___x_900_, 1);
v___y_857_ = v_val_902_;
goto v___jp_856_;
}
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0));
lean_inc(v_ref_851_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v_ref_851_);
lean_ctor_set(v___x_904_, 1, v_ps_855_);
if (v_explicit_853_ == 0)
{
lean_dec(v_ref_851_);
v___y_884_ = v___x_903_;
v___y_885_ = v___x_904_;
goto v___jp_883_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_905_, 0, v_ref_851_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___y_884_ = v___x_903_;
v___y_885_ = v___x_905_;
goto v___jp_883_;
}
}
}
}
else
{
if (lean_obj_tag(v_ps_855_) == 0)
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_880_ = v___x_892_;
v___y_881_ = v___x_906_;
goto v___jp_879_;
}
else
{
lean_object* v_head_907_; 
v_head_907_ = lean_ctor_get(v_ps_855_, 0);
lean_inc(v_head_907_);
v___y_880_ = v___x_892_;
v___y_881_ = v_head_907_;
goto v___jp_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___boxed(lean_object* v_ref_930_, lean_object* v_info_931_, lean_object* v_explicit_932_, lean_object* v_idx_933_, lean_object* v_ps_934_){
_start:
{
uint8_t v_explicit_boxed_935_; lean_object* v_res_936_; 
v_explicit_boxed_935_ = lean_unbox(v_explicit_932_);
v_res_936_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_930_, v_info_931_, v_explicit_boxed_935_, v_idx_933_, v_ps_934_);
lean_dec(v_idx_933_);
lean_dec_ref(v_info_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter___redArg(lean_object* v_x_937_, lean_object* v_h__1_938_){
_start:
{
lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_941_; 
v_fst_939_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_fst_939_);
v_snd_940_ = lean_ctor_get(v_x_937_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v_x_937_);
v___x_941_ = lean_apply_2(v_h__1_938_, v_fst_939_, v_snd_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter(lean_object* v_motive_942_, lean_object* v_x_943_, lean_object* v_h__1_944_){
_start:
{
lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_947_; 
v_fst_945_ = lean_ctor_get(v_x_943_, 0);
lean_inc(v_fst_945_);
v_snd_946_ = lean_ctor_get(v_x_943_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v_x_943_);
v___x_947_ = lean_apply_2(v_h__1_944_, v_fst_945_, v_snd_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter___redArg(lean_object* v_ps_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_, lean_object* v_h__3_951_){
_start:
{
if (lean_obj_tag(v_ps_948_) == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_h__3_951_);
lean_dec(v_h__2_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_apply_1(v_h__1_949_, v___x_952_);
return v___x_953_;
}
else
{
lean_object* v_tail_954_; 
lean_dec(v_h__1_949_);
v_tail_954_ = lean_ctor_get(v_ps_948_, 1);
if (lean_obj_tag(v_tail_954_) == 0)
{
lean_object* v_head_955_; lean_object* v___x_956_; 
lean_dec(v_h__3_951_);
v_head_955_ = lean_ctor_get(v_ps_948_, 0);
lean_inc(v_head_955_);
lean_dec_ref_known(v_ps_948_, 2);
v___x_956_ = lean_apply_1(v_h__2_950_, v_head_955_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
lean_dec(v_h__2_950_);
v___x_957_ = lean_apply_3(v_h__3_951_, v_ps_948_, lean_box(0), lean_box(0));
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter(lean_object* v_motive_958_, lean_object* v_ps_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_, lean_object* v_h__3_962_){
_start:
{
if (lean_obj_tag(v_ps_959_) == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_h__3_962_);
lean_dec(v_h__2_961_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_1(v_h__1_960_, v___x_963_);
return v___x_964_;
}
else
{
lean_object* v_tail_965_; 
lean_dec(v_h__1_960_);
v_tail_965_ = lean_ctor_get(v_ps_959_, 1);
if (lean_obj_tag(v_tail_965_) == 0)
{
lean_object* v_head_966_; lean_object* v___x_967_; 
lean_dec(v_h__3_962_);
v_head_966_ = lean_ctor_get(v_ps_959_, 0);
lean_inc(v_head_966_);
lean_dec_ref_known(v_ps_959_, 2);
v___x_967_ = lean_apply_1(v_h__2_961_, v_head_966_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; 
lean_dec(v_h__2_961_);
v___x_968_ = lean_apply_3(v_h__3_962_, v_ps_959_, lean_box(0), lean_box(0));
return v___x_968_;
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
lean_ctor_set(v___x_974_, 4, v___x_972_);
lean_ctor_set(v___x_974_, 5, v___x_972_);
lean_ctor_set(v___x_974_, 6, v___x_972_);
lean_ctor_set(v___x_974_, 7, v___x_972_);
lean_ctor_set(v___x_974_, 8, v___x_972_);
lean_ctor_set(v___x_974_, 9, v___x_972_);
lean_ctor_set(v___x_974_, 10, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(32u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_978_ = ((size_t)5ULL);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_unsigned_to_nat(32u);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_983_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
lean_ctor_set(v___x_983_, 2, v___x_979_);
lean_ctor_set(v___x_983_, 3, v___x_979_);
lean_ctor_set_usize(v___x_983_, 4, v___x_978_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_984_ = lean_box(1);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_984_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1009_, lean_object* v_declHint_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_env_1015_; uint8_t v___x_1016_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_st_ref_get(v___y_1011_);
v_env_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_env_1015_);
lean_dec(v___x_1014_);
v___x_1016_ = l_Lean_Name_isAnonymous(v_declHint_1010_);
if (v___x_1016_ == 0)
{
uint8_t v_isExporting_1017_; 
v_isExporting_1017_ = lean_ctor_get_uint8(v_env_1015_, sizeof(void*)*8);
if (v_isExporting_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_env_1015_);
lean_dec(v_declHint_1010_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_msg_1009_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
lean_inc_ref(v_env_1015_);
v___x_1019_ = l_Lean_Environment_setExporting(v_env_1015_, v___x_1016_);
lean_inc(v_declHint_1010_);
lean_inc_ref(v___x_1019_);
v___x_1020_ = l_Lean_Environment_contains(v___x_1019_, v_declHint_1010_, v_isExporting_1017_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v___x_1019_);
lean_dec_ref(v_env_1015_);
lean_dec(v_declHint_1010_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_msg_1009_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_c_1027_; lean_object* v___x_1028_; 
v___x_1022_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1024_ = l_Lean_Options_empty;
v___x_1025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1019_);
lean_ctor_set(v___x_1025_, 1, v___x_1022_);
lean_ctor_set(v___x_1025_, 2, v___x_1023_);
lean_ctor_set(v___x_1025_, 3, v___x_1024_);
lean_inc(v_declHint_1010_);
v___x_1026_ = l_Lean_MessageData_ofConstName(v_declHint_1010_, v___x_1016_);
v_c_1027_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1027_, 0, v___x_1025_);
lean_ctor_set(v_c_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1015_, v_declHint_1010_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v_env_1015_);
lean_dec(v_declHint_1010_);
v___x_1029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_c_1027_);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_MessageData_note(v___x_1032_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_msg_1009_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1070_; 
v_val_1036_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1038_ = v___x_1028_;
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v___x_1028_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_mod_1042_; uint8_t v___x_1043_; 
v___x_1040_ = l_Lean_Environment_header(v_env_1015_);
lean_dec_ref(v_env_1015_);
v___x_1041_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1040_);
v_mod_1042_ = lean_array_get(v___x_1013_, v___x_1041_, v_val_1036_);
lean_dec(v_val_1036_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Lean_isPrivateName(v_declHint_1010_);
lean_dec(v_declHint_1010_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1027_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofName(v_mod_1042_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_MessageData_note(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_1009_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1053_);
v___x_1055_ = v___x_1038_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_c_1027_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_ofName(v_mod_1042_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_note(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1009_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1066_);
v___x_1068_ = v___x_1038_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_env_1015_);
lean_dec(v_declHint_1010_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_msg_1009_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1072_, v_declHint_1073_, v___y_1074_);
lean_dec(v___y_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_msg_1077_, lean_object* v_declHint_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1094_; 
v___x_1084_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1077_, v_declHint_1078_, v___y_1082_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = l_Lean_unknownIdentifierMessageTag;
v___x_1090_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1095_, lean_object* v_declHint_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1095_, v_declHint_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v_toCold_1112_; lean_object* v_mctx_1113_; lean_object* v_lctx_1114_; lean_object* v_options_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_st_ref_get(v___y_1105_);
v_toCold_1112_ = lean_ctor_get(v___y_1106_, 0);
v_mctx_1113_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_mctx_1113_);
lean_dec(v___x_1111_);
v_lctx_1114_ = lean_ctor_get(v___y_1104_, 2);
v_options_1115_ = lean_ctor_get(v_toCold_1112_, 2);
lean_inc_ref(v_options_1115_);
lean_inc_ref(v_lctx_1114_);
v___x_1116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1116_, 0, v_env_1110_);
lean_ctor_set(v___x_1116_, 1, v_mctx_1113_);
lean_ctor_set(v___x_1116_, 2, v_lctx_1114_);
lean_ctor_set(v___x_1116_, 3, v_options_1115_);
v___x_1117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_msgData_1103_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msgData_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_ref_1132_ = lean_ctor_get(v___y_1129_, 2);
v___x_1133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_inc(v_ref_1132_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_ref_1132_);
lean_ctor_set(v___x_1138_, 1, v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1150_, lean_object* v_msg_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_toCold_1157_; lean_object* v_currRecDepth_1158_; lean_object* v_ref_1159_; uint16_t v_optionFlags_1160_; uint8_t v_suppressElabErrors_1161_; uint8_t v_isRecordingDeps_1162_; lean_object* v_ref_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_toCold_1157_ = lean_ctor_get(v___y_1154_, 0);
v_currRecDepth_1158_ = lean_ctor_get(v___y_1154_, 1);
v_ref_1159_ = lean_ctor_get(v___y_1154_, 2);
v_optionFlags_1160_ = lean_ctor_get_uint16(v___y_1154_, sizeof(void*)*3);
v_suppressElabErrors_1161_ = lean_ctor_get_uint8(v___y_1154_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1162_ = lean_ctor_get_uint8(v___y_1154_, sizeof(void*)*3 + 3);
v_ref_1163_ = l_Lean_replaceRef(v_ref_1150_, v_ref_1159_);
lean_inc(v_currRecDepth_1158_);
lean_inc_ref(v_toCold_1157_);
v___x_1164_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1164_, 0, v_toCold_1157_);
lean_ctor_set(v___x_1164_, 1, v_currRecDepth_1158_);
lean_ctor_set(v___x_1164_, 2, v_ref_1163_);
lean_ctor_set_uint16(v___x_1164_, sizeof(void*)*3, v_optionFlags_1160_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 2, v_suppressElabErrors_1161_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 3, v_isRecordingDeps_1162_);
v___x_1165_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1151_, v___y_1152_, v___y_1153_, v___x_1164_, v___y_1155_);
lean_dec_ref_known(v___x_1164_, 3);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1166_, lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1166_, v_msg_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v_ref_1166_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1174_, lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_a_1183_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1174_, v_a_1183_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1185_, lean_object* v_msg_1186_, lean_object* v_declHint_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1185_, v_msg_1186_, v_declHint_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v_ref_1185_);
return v_res_1193_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1200_, lean_object* v_constName_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1207_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1208_ = 0;
lean_inc(v_constName_1201_);
v___x_1209_ = l_Lean_MessageData_ofConstName(v_constName_1201_, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1207_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1200_, v___x_1212_, v_constName_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1214_, lean_object* v_constName_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1214_, v_constName_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v_ref_1214_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_ref_1228_; lean_object* v___x_1229_; 
v_ref_1228_ = lean_ctor_get(v___y_1225_, 2);
v___x_1229_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1228_, v_constName_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object* v_constName_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_env_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_st_ref_get(v___y_1241_);
v_env_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_env_1244_);
lean_dec(v___x_1243_);
v___x_1245_ = 0;
lean_inc(v_constName_1237_);
v___x_1246_ = l_Lean_Environment_findConstVal_x3f(v_env_1244_, v_constName_1237_, v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_constName_1237_);
v_val_1248_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1246_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_val_1248_);
lean_dec(v___x_1246_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 0);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_val_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object* v_constName_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
if (lean_obj_tag(v_a_1263_) == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = l_List_reverse___redArg(v_a_1264_);
return v___x_1265_;
}
else
{
lean_object* v_head_1266_; lean_object* v_tail_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1276_; 
v_head_1266_ = lean_ctor_get(v_a_1263_, 0);
v_tail_1267_ = lean_ctor_get(v_a_1263_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_a_1263_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1269_ = v_a_1263_;
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_tail_1267_);
lean_inc(v_head_1266_);
lean_dec(v_a_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = l_Lean_mkLevelParam(v_head_1266_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_a_1264_);
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_a_1264_);
v___x_1273_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v_a_1263_ = v_tail_1267_;
v_a_1264_ = v___x_1273_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
lean_inc(v_constName_1277_);
v___x_1283_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1295_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_levelParams_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_levelParams_1288_ = lean_ctor_get(v_a_1284_, 1);
lean_inc(v_levelParams_1288_);
lean_dec(v_a_1284_);
v___x_1289_ = lean_box(0);
v___x_1290_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(v_levelParams_1288_, v___x_1289_);
v___x_1291_ = l_Lean_mkConst(v_constName_1277_, v___x_1290_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1291_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_constName_1277_);
v_a_1296_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1283_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1283_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_constName_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object* v_ref_1311_, lean_object* v_params_1312_, lean_object* v_altVarNames_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_x_1315_);
lean_dec(v_ref_1311_);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_altVarNames_1313_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v_head_1324_; lean_object* v_tail_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1431_; 
v_head_1324_ = lean_ctor_get(v_x_1314_, 0);
v_tail_1325_ = lean_ctor_get(v_x_1314_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1327_ = v_x_1314_;
v_isShared_1328_ = v_isSharedCheck_1431_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_tail_1325_);
lean_inc(v_head_1324_);
lean_dec(v_x_1314_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1431_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; 
lean_inc(v_head_1324_);
v___x_1329_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_head_1324_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = lean_box(0);
v___x_1332_ = l_Lean_Meta_getFunInfo(v_a_1330_, v___x_1331_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_paramInfo_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1413_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v_paramInfo_1334_ = lean_ctor_get(v_a_1333_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1333_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_a_1333_, 1);
lean_dec(v_unused_1414_);
v___x_1336_ = v_a_1333_;
v_isShared_1337_ = v_isSharedCheck_1413_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_paramInfo_1334_);
lean_dec(v_a_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1413_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1378_; uint8_t v_fst_1379_; lean_object* v_snd_1380_; lean_object* v_snd_1381_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1408_; 
if (lean_obj_tag(v_x_1315_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_1408_ = v___x_1411_;
goto v___jp_1407_;
}
else
{
lean_object* v_head_1412_; 
v_head_1412_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_head_1412_);
v___y_1408_ = v_head_1412_;
goto v___jp_1407_;
}
v___jp_1338_:
{
lean_object* v___x_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1376_; 
v___x_1343_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1342_, v_paramInfo_1334_, v___y_1341_, v_params_1312_, v___y_1340_);
lean_dec_ref(v_paramInfo_1334_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
v_snd_1345_ = lean_ctor_get(v___x_1343_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1347_ = v___x_1343_;
v_isShared_1348_ = v_isSharedCheck_1376_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v___x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1376_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = 1;
v___x_1350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1350_, 0, v_fst_1344_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*1, v___x_1349_);
v___x_1351_ = lean_array_push(v_altVarNames_1313_, v___x_1350_);
v___x_1352_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1311_, v_params_1312_, v___x_1351_, v_tail_1325_, v___y_1339_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1375_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1375_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1375_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; lean_object* v_snd_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1374_; 
v_fst_1357_ = lean_ctor_get(v_a_1353_, 0);
v_snd_1358_ = lean_ctor_get(v_a_1353_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1353_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1360_ = v_a_1353_;
v_isShared_1361_ = v_isSharedCheck_1374_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_snd_1358_);
lean_inc(v_fst_1357_);
lean_dec(v_a_1353_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1374_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v_snd_1345_);
lean_ctor_set(v___x_1360_, 0, v_head_1324_);
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_head_1324_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1345_);
v___x_1363_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_snd_1358_);
lean_ctor_set(v___x_1327_, 0, v___x_1363_);
v___x_1365_ = v___x_1327_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1358_);
v___x_1365_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1365_);
lean_ctor_set(v___x_1347_, 0, v_fst_1357_);
v___x_1367_ = v___x_1347_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_fst_1357_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1367_);
v___x_1369_ = v___x_1355_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_del_object(v___x_1327_);
lean_dec(v_head_1324_);
return v___x_1352_;
}
}
}
v___jp_1377_:
{
lean_object* v_ref_1382_; 
v_ref_1382_ = lean_ctor_get(v___y_1378_, 0);
lean_inc(v_ref_1382_);
lean_dec_ref(v___y_1378_);
v___y_1339_ = v_snd_1381_;
v___y_1340_ = v_snd_1380_;
v___y_1341_ = v_fst_1379_;
v___y_1342_ = v_ref_1382_;
goto v___jp_1338_;
}
v___jp_1383_:
{
lean_object* v___x_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; uint8_t v___x_1389_; 
lean_inc_ref(v___y_1385_);
v___x_1386_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1385_);
v_fst_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v___x_1386_);
v___x_1389_ = lean_unbox(v_fst_1387_);
lean_dec(v_fst_1387_);
v___y_1378_ = v___y_1385_;
v_fst_1379_ = v___x_1389_;
v_snd_1380_ = v_snd_1388_;
v_snd_1381_ = v___y_1384_;
goto v___jp_1377_;
}
v___jp_1390_:
{
if (lean_obj_tag(v_tail_1325_) == 0)
{
if (lean_obj_tag(v___y_1393_) == 1)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1404_; 
v_isSharedCheck_1404_ = !lean_is_exclusive(v___y_1393_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1405_ = lean_ctor_get(v___y_1393_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v___y_1393_, 0);
lean_dec(v_unused_1406_);
v___x_1395_ = v___y_1393_;
v_isShared_1396_ = v_isSharedCheck_1404_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___y_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1404_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
uint8_t v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = 0;
lean_inc(v_ref_1311_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 6);
lean_ctor_set(v___x_1336_, 1, v_x_1315_);
lean_ctor_set(v___x_1336_, 0, v_ref_1311_);
v___x_1399_ = v___x_1336_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_ref_1311_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_x_1315_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
lean_inc(v___y_1391_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___y_1391_);
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1401_ = v___x_1395_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___y_1391_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1378_ = v___y_1392_;
v_fst_1379_ = v___x_1397_;
v_snd_1380_ = v___x_1401_;
v_snd_1381_ = v___y_1391_;
goto v___jp_1377_;
}
}
}
}
else
{
lean_dec(v___y_1391_);
lean_del_object(v___x_1336_);
lean_dec(v_x_1315_);
v___y_1384_ = v___y_1393_;
v___y_1385_ = v___y_1392_;
goto v___jp_1383_;
}
}
else
{
lean_dec(v___y_1391_);
lean_del_object(v___x_1336_);
lean_dec(v_x_1315_);
v___y_1384_ = v___y_1393_;
v___y_1385_ = v___y_1392_;
goto v___jp_1383_;
}
}
v___jp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_box(0);
if (lean_obj_tag(v_x_1315_) == 0)
{
v___y_1391_ = v___x_1409_;
v___y_1392_ = v___y_1408_;
v___y_1393_ = v___x_1409_;
goto v___jp_1390_;
}
else
{
lean_object* v_tail_1410_; 
v_tail_1410_ = lean_ctor_get(v_x_1315_, 1);
lean_inc(v_tail_1410_);
v___y_1391_ = v___x_1409_;
v___y_1392_ = v___y_1408_;
v___y_1393_ = v_tail_1410_;
goto v___jp_1390_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1327_);
lean_dec(v_tail_1325_);
lean_dec(v_head_1324_);
lean_dec(v_x_1315_);
lean_dec_ref(v_altVarNames_1313_);
lean_dec(v_ref_1311_);
v_a_1415_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1332_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1332_);
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
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_del_object(v___x_1327_);
lean_dec(v_tail_1325_);
lean_dec(v_head_1324_);
lean_dec(v_x_1315_);
lean_dec_ref(v_altVarNames_1313_);
lean_dec(v_ref_1311_);
v_a_1423_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1329_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1329_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object* v_ref_1432_, lean_object* v_params_1433_, lean_object* v_altVarNames_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1432_, v_params_1433_, v_altVarNames_1434_, v_x_1435_, v_x_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_params_1433_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1443_, lean_object* v_constName_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_constName_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(v_00_u03b1_1451_, v_constName_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1459_, lean_object* v_ref_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1460_, v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_ref_1469_, lean_object* v_constName_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1468_, v_ref_1469_, v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_ref_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1477_, lean_object* v_ref_1478_, lean_object* v_msg_1479_, lean_object* v_declHint_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1478_, v_msg_1479_, v_declHint_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_ref_1488_, lean_object* v_msg_1489_, lean_object* v_declHint_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1487_, v_ref_1488_, v_msg_1489_, v_declHint_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v_ref_1488_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_1497_, lean_object* v_declHint_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1497_, v_declHint_1498_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1505_, lean_object* v_declHint_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(v_msg_1505_, v_declHint_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1513_, lean_object* v_ref_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1514_, v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1522_, v_ref_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v_ref_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1531_, lean_object* v_msg_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1539_, lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1539_, v_msg_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object* v_e_1547_, lean_object* v_cont_1548_, lean_object* v_g_1549_, lean_object* v_fs_1550_, lean_object* v_clears_1551_, lean_object* v_a_1552_, lean_object* v_ref_1553_, lean_object* v_a_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Lean_Expr_isFVar(v_e_1547_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec(v_ref_1553_);
lean_dec_ref(v_e_1547_);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___x_1563_ = lean_apply_11(v_cont_1548_, v_g_1549_, v_fs_1550_, v_clears_1551_, v_a_1552_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_1553_, v_e_1547_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1564_, 1);
lean_inc(v___y_1560_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
v___x_1565_ = lean_apply_11(v_cont_1548_, v_g_1549_, v_fs_1550_, v_clears_1551_, v_a_1552_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, lean_box(0));
return v___x_1565_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1552_);
lean_dec_ref(v_clears_1551_);
lean_dec(v_fs_1550_);
lean_dec(v_g_1549_);
lean_dec_ref(v_cont_1548_);
v_a_1566_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1564_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object* v_e_1574_, lean_object* v_cont_1575_, lean_object* v_g_1576_, lean_object* v_fs_1577_, lean_object* v_clears_1578_, lean_object* v_a_1579_, lean_object* v_ref_1580_, lean_object* v_a_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(v_e_1574_, v_cont_1575_, v_g_1576_, v_fs_1577_, v_clears_1578_, v_a_1579_, v_ref_1580_, v_a_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v_a_1581_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object* v_x_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
v___x_1598_ = lean_apply_7(v_x_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, lean_box(0));
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object* v_x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object* v_mvarId_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; 
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1617_, 0, v_x_1609_);
lean_closure_set(v___f_1617_, 1, v___y_1610_);
lean_closure_set(v___f_1617_, 2, v___y_1611_);
v___x_1618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1608_, v___f_1617_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1618_) == 0)
{
return v___x_1618_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object* v_mvarId_1627_, lean_object* v_x_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_1627_, v_x_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1636_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object* v_x_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 1)
{
lean_object* v_fvarId_1649_; lean_object* v___x_1650_; 
v_fvarId_1649_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_fvarId_1649_);
lean_dec_ref_known(v_x_1643_, 1);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_fvarId_1649_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1652_ = l_Lean_MessageData_ofExpr(v_x_1643_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v___x_1655_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object* v_x_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(v_x_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1663_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
return v_x_1669_;
}
else
{
lean_object* v_head_1671_; lean_object* v_tail_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1694_; 
v_head_1671_ = lean_ctor_get(v_x_1670_, 0);
v_tail_1672_ = lean_ctor_get(v_x_1670_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1670_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1674_ = v_x_1670_;
v_isShared_1675_ = v_isSharedCheck_1694_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_tail_1672_);
lean_inc(v_head_1671_);
lean_dec(v_x_1670_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1694_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_before_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1692_; 
v_before_1676_ = lean_ctor_get(v_head_1671_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_head_1671_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_head_1671_, 1);
lean_dec(v_unused_1693_);
v___x_1678_ = v_head_1671_;
v_isShared_1679_ = v_isSharedCheck_1692_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_before_1676_);
lean_dec(v_head_1671_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1692_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 7);
lean_ctor_set(v___x_1678_, 1, v___x_1680_);
lean_ctor_set(v___x_1678_, 0, v_x_1669_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_x_1669_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 7);
lean_ctor_set(v___x_1674_, 1, v___x_1683_);
lean_ctor_set(v___x_1674_, 0, v___x_1682_);
v___x_1685_ = v___x_1674_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_MessageData_ofSyntax(v_before_1676_);
v___x_1687_ = l_Lean_indentD(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1685_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v_x_1669_ = v___x_1688_;
v_x_1670_ = v_tail_1672_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_1695_, lean_object* v_opt_1696_){
_start:
{
lean_object* v_name_1697_; lean_object* v_defValue_1698_; lean_object* v_map_1699_; lean_object* v___x_1700_; 
v_name_1697_ = lean_ctor_get(v_opt_1696_, 0);
v_defValue_1698_ = lean_ctor_get(v_opt_1696_, 1);
v_map_1699_ = lean_ctor_get(v_opts_1695_, 0);
v___x_1700_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1699_, v_name_1697_);
if (lean_obj_tag(v___x_1700_) == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_unbox(v_defValue_1698_);
return v___x_1701_;
}
else
{
lean_object* v_val_1702_; 
v_val_1702_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_val_1702_);
lean_dec_ref_known(v___x_1700_, 1);
if (lean_obj_tag(v_val_1702_) == 1)
{
uint8_t v_v_1703_; 
v_v_1703_ = lean_ctor_get_uint8(v_val_1702_, 0);
lean_dec_ref_known(v_val_1702_, 0);
return v_v_1703_;
}
else
{
uint8_t v___x_1704_; 
lean_dec(v_val_1702_);
v___x_1704_ = lean_unbox(v_defValue_1698_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_1705_, lean_object* v_opt_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_1705_, v_opt_1706_);
lean_dec_ref(v_opt_1706_);
lean_dec_ref(v_opts_1705_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_1713_ = l_Lean_MessageData_ofFormat(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_1714_, lean_object* v_macroStack_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1718_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1716_);
v___x_1719_ = l_Lean_Elab_pp_macroStack;
v___x_1720_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v___x_1718_, v___x_1719_);
lean_dec_ref(v___x_1718_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; 
lean_dec(v_macroStack_1715_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_msgData_1714_);
return v___x_1721_;
}
else
{
if (lean_obj_tag(v_macroStack_1715_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_msgData_1714_);
return v___x_1722_;
}
else
{
lean_object* v_head_1723_; lean_object* v_after_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1739_; 
v_head_1723_ = lean_ctor_get(v_macroStack_1715_, 0);
lean_inc(v_head_1723_);
v_after_1724_ = lean_ctor_get(v_head_1723_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_head_1723_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_head_1723_, 0);
lean_dec(v_unused_1740_);
v___x_1726_ = v_head_1723_;
v_isShared_1727_ = v_isSharedCheck_1739_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_after_1724_);
lean_dec(v_head_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1739_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 7);
lean_ctor_set(v___x_1726_, 1, v___x_1728_);
lean_ctor_set(v___x_1726_, 0, v_msgData_1714_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_msgData_1714_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_msgData_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1731_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_MessageData_ofSyntax(v_after_1724_);
v___x_1734_ = l_Lean_indentD(v___x_1733_);
v_msgData_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1735_, 0, v___x_1732_);
lean_ctor_set(v_msgData_1735_, 1, v___x_1734_);
v___x_1736_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_1735_, v_macroStack_1715_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_1741_, lean_object* v_macroStack_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_1741_, v_macroStack_1742_, v___y_1743_);
lean_dec_ref(v___y_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_ref_1754_; lean_object* v_macroStack_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_ref_1754_ = lean_ctor_get(v___y_1751_, 2);
v_macroStack_1755_ = lean_ctor_get(v___y_1747_, 1);
v___x_1756_ = l_Lean_Elab_getBetterRef(v_ref_1754_, v_macroStack_1755_);
v___x_1757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1746_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
lean_inc(v_macroStack_1755_);
v___x_1759_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_1758_, v_macroStack_1755_, v___y_1751_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1756_);
lean_ctor_set(v___x_1764_, 1, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(lean_object* v_e_1784_, lean_object* v_a_1785_, lean_object* v_00_u03b1_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1795_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1796_ = l_Lean_MessageData_ofExpr(v_e_1784_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Lean_MessageData_ofExpr(v_a_1785_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_1803_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v_e_1805_, lean_object* v_a_1806_, lean_object* v_00_u03b1_1807_, lean_object* v_x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_1805_, v_a_1806_, v_00_u03b1_1807_, v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1816_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
if (lean_obj_tag(v_x_1818_) == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = 1;
return v___x_1819_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = 0;
return v___x_1820_;
}
}
else
{
if (lean_obj_tag(v_x_1818_) == 0)
{
uint8_t v___x_1821_; 
v___x_1821_ = 0;
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; lean_object* v_val_1823_; uint8_t v___x_1824_; 
v_val_1822_ = lean_ctor_get(v_x_1817_, 0);
v_val_1823_ = lean_ctor_get(v_x_1818_, 0);
v___x_1824_ = lean_name_eq(v_val_1822_, v_val_1823_);
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_1825_, lean_object* v_x_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_1825_, v_x_1826_);
lean_dec(v_x_1826_);
lean_dec(v_x_1825_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object* v_x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
lean_object* v_ks_1833_; lean_object* v_vs_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1858_; 
v_ks_1833_ = lean_ctor_get(v_x_1829_, 0);
v_vs_1834_ = lean_ctor_get(v_x_1829_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1836_ = v_x_1829_;
v_isShared_1837_ = v_isSharedCheck_1858_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_vs_1834_);
lean_inc(v_ks_1833_);
lean_dec(v_x_1829_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1858_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_ks_1833_);
v___x_1839_ = lean_nat_dec_lt(v_x_1830_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec(v_x_1830_);
v___x_1840_ = lean_array_push(v_ks_1833_, v_x_1831_);
v___x_1841_ = lean_array_push(v_vs_1834_, v_x_1832_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v___x_1841_);
lean_ctor_set(v___x_1836_, 0, v___x_1840_);
v___x_1843_ = v___x_1836_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v_k_x27_1845_; uint8_t v___x_1846_; 
v_k_x27_1845_ = lean_array_fget_borrowed(v_ks_1833_, v_x_1830_);
v___x_1846_ = l_Lean_instBEqMVarId_beq(v_x_1831_, v_k_x27_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1848_; 
if (v_isShared_1837_ == 0)
{
v___x_1848_ = v___x_1836_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_ks_1833_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_vs_1834_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_unsigned_to_nat(1u);
v___x_1850_ = lean_nat_add(v_x_1830_, v___x_1849_);
lean_dec(v_x_1830_);
v_x_1829_ = v___x_1848_;
v_x_1830_ = v___x_1850_;
goto _start;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = lean_array_fset(v_ks_1833_, v_x_1830_, v_x_1831_);
v___x_1854_ = lean_array_fset(v_vs_1834_, v_x_1830_, v_x_1832_);
lean_dec(v_x_1830_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v___x_1854_);
lean_ctor_set(v___x_1836_, 0, v___x_1853_);
v___x_1856_ = v___x_1836_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object* v_n_1859_, lean_object* v_k_1860_, lean_object* v_v_1861_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_n_1859_, v___x_1862_, v_k_1860_, v_v_1861_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object* v_x_1865_, size_t v_x_1866_, size_t v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v_es_1870_; size_t v___x_1871_; size_t v___x_1872_; lean_object* v_j_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_es_1870_ = lean_ctor_get(v_x_1865_, 0);
v___x_1871_ = ((size_t)31ULL);
v___x_1872_ = lean_usize_land(v_x_1866_, v___x_1871_);
v_j_1873_ = lean_usize_to_nat(v___x_1872_);
v___x_1874_ = lean_array_get_size(v_es_1870_);
v___x_1875_ = lean_nat_dec_lt(v_j_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_dec(v_j_1873_);
lean_dec(v_x_1869_);
lean_dec(v_x_1868_);
return v_x_1865_;
}
else
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1914_; 
lean_inc_ref(v_es_1870_);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_x_1865_, 0);
lean_dec(v_unused_1915_);
v___x_1877_ = v_x_1865_;
v_isShared_1878_ = v_isSharedCheck_1914_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v_x_1865_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1914_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_v_1879_; lean_object* v___x_1880_; lean_object* v_xs_x27_1881_; lean_object* v___y_1883_; 
v_v_1879_ = lean_array_fget(v_es_1870_, v_j_1873_);
v___x_1880_ = lean_box(0);
v_xs_x27_1881_ = lean_array_fset(v_es_1870_, v_j_1873_, v___x_1880_);
switch(lean_obj_tag(v_v_1879_))
{
case 0:
{
lean_object* v_key_1888_; lean_object* v_val_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1899_; 
v_key_1888_ = lean_ctor_get(v_v_1879_, 0);
v_val_1889_ = lean_ctor_get(v_v_1879_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_v_1879_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1891_ = v_v_1879_;
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_val_1889_);
lean_inc(v_key_1888_);
lean_dec(v_v_1879_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint8_t v___x_1893_; 
v___x_1893_ = l_Lean_instBEqMVarId_beq(v_x_1868_, v_key_1888_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_del_object(v___x_1891_);
v___x_1894_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1888_, v_val_1889_, v_x_1868_, v_x_1869_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
v___y_1883_ = v___x_1895_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1897_; 
lean_dec(v_val_1889_);
lean_dec(v_key_1888_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_x_1869_);
lean_ctor_set(v___x_1891_, 0, v_x_1868_);
v___x_1897_ = v___x_1891_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_x_1868_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_x_1869_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
v___y_1883_ = v___x_1897_;
goto v___jp_1882_;
}
}
}
}
case 1:
{
lean_object* v_node_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1912_; 
v_node_1900_ = lean_ctor_get(v_v_1879_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_v_1879_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1902_ = v_v_1879_;
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_node_1900_);
lean_dec(v_v_1879_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1904_ = ((size_t)5ULL);
v___x_1905_ = lean_usize_shift_right(v_x_1866_, v___x_1904_);
v___x_1906_ = ((size_t)1ULL);
v___x_1907_ = lean_usize_add(v_x_1867_, v___x_1906_);
v___x_1908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_node_1900_, v___x_1905_, v___x_1907_, v_x_1868_, v_x_1869_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1908_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v___y_1883_ = v___x_1910_;
goto v___jp_1882_;
}
}
}
default: 
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_x_1868_);
lean_ctor_set(v___x_1913_, 1, v_x_1869_);
v___y_1883_ = v___x_1913_;
goto v___jp_1882_;
}
}
v___jp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_array_fset(v_xs_x27_1881_, v_j_1873_, v___y_1883_);
lean_dec(v_j_1873_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1884_);
v___x_1886_ = v___x_1877_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_ks_1916_; lean_object* v_vs_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1935_; 
v_ks_1916_ = lean_ctor_get(v_x_1865_, 0);
v_vs_1917_ = lean_ctor_get(v_x_1865_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1919_ = v_x_1865_;
v_isShared_1920_ = v_isSharedCheck_1935_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_vs_1917_);
lean_inc(v_ks_1916_);
lean_dec(v_x_1865_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1935_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_ks_1916_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_vs_1917_);
v___x_1922_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v_newNode_1923_; size_t v___x_1924_; uint8_t v___x_1925_; 
v_newNode_1923_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1922_, v_x_1868_, v_x_1869_);
v___x_1924_ = ((size_t)7ULL);
v___x_1925_ = lean_usize_dec_le(v___x_1924_, v_x_1867_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1926_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1923_);
v___x_1927_ = lean_unsigned_to_nat(4u);
v___x_1928_ = lean_nat_dec_lt(v___x_1926_, v___x_1927_);
lean_dec(v___x_1926_);
if (v___x_1928_ == 0)
{
lean_object* v_ks_1929_; lean_object* v_vs_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_ks_1929_ = lean_ctor_get(v_newNode_1923_, 0);
lean_inc_ref(v_ks_1929_);
v_vs_1930_ = lean_ctor_get(v_newNode_1923_, 1);
lean_inc_ref(v_vs_1930_);
lean_dec_ref(v_newNode_1923_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1867_, v_ks_1929_, v_vs_1930_, v___x_1931_, v___x_1932_);
lean_dec_ref(v_vs_1930_);
lean_dec_ref(v_ks_1929_);
return v___x_1933_;
}
else
{
return v_newNode_1923_;
}
}
else
{
return v_newNode_1923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1936_, lean_object* v_keys_1937_, lean_object* v_vals_1938_, lean_object* v_i_1939_, lean_object* v_entries_1940_){
_start:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_array_get_size(v_keys_1937_);
v___x_1942_ = lean_nat_dec_lt(v_i_1939_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec(v_i_1939_);
return v_entries_1940_;
}
else
{
lean_object* v_k_1943_; lean_object* v_v_1944_; uint64_t v___x_1945_; size_t v_h_1946_; size_t v___x_1947_; lean_object* v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v_h_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_k_1943_ = lean_array_fget_borrowed(v_keys_1937_, v_i_1939_);
v_v_1944_ = lean_array_fget_borrowed(v_vals_1938_, v_i_1939_);
v___x_1945_ = l_Lean_instHashableMVarId_hash(v_k_1943_);
v_h_1946_ = lean_uint64_to_usize(v___x_1945_);
v___x_1947_ = ((size_t)5ULL);
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_sub(v_depth_1936_, v___x_1949_);
v___x_1951_ = lean_usize_mul(v___x_1947_, v___x_1950_);
v_h_1952_ = lean_usize_shift_right(v_h_1946_, v___x_1951_);
v___x_1953_ = lean_nat_add(v_i_1939_, v___x_1948_);
lean_dec(v_i_1939_);
lean_inc(v_v_1944_);
lean_inc(v_k_1943_);
v___x_1954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1940_, v_h_1952_, v_depth_1936_, v_k_1943_, v_v_1944_);
v_i_1939_ = v___x_1953_;
v_entries_1940_ = v___x_1954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1956_, lean_object* v_keys_1957_, lean_object* v_vals_1958_, lean_object* v_i_1959_, lean_object* v_entries_1960_){
_start:
{
size_t v_depth_boxed_1961_; lean_object* v_res_1962_; 
v_depth_boxed_1961_ = lean_unbox_usize(v_depth_1956_);
lean_dec(v_depth_1956_);
v_res_1962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1961_, v_keys_1957_, v_vals_1958_, v_i_1959_, v_entries_1960_);
lean_dec_ref(v_vals_1958_);
lean_dec_ref(v_keys_1957_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
size_t v_x_18794__boxed_1968_; size_t v_x_18795__boxed_1969_; lean_object* v_res_1970_; 
v_x_18794__boxed_1968_ = lean_unbox_usize(v_x_1964_);
lean_dec(v_x_1964_);
v_x_18795__boxed_1969_ = lean_unbox_usize(v_x_1965_);
lean_dec(v_x_1965_);
v_res_1970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1963_, v_x_18794__boxed_1968_, v_x_18795__boxed_1969_, v_x_1966_, v_x_1967_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_){
_start:
{
uint64_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = l_Lean_instHashableMVarId_hash(v_x_1972_);
v___x_1975_ = lean_uint64_to_usize(v___x_1974_);
v___x_1976_ = ((size_t)1ULL);
v___x_1977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1971_, v___x_1975_, v___x_1976_, v_x_1972_, v_x_1973_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1978_, lean_object* v_val_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_mctx_1983_; lean_object* v_cache_1984_; lean_object* v_zetaDeltaFVarIds_1985_; lean_object* v_postponed_1986_; lean_object* v_diag_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2016_; 
v___x_1982_ = lean_st_ref_take(v___y_1980_);
v_mctx_1983_ = lean_ctor_get(v___x_1982_, 0);
v_cache_1984_ = lean_ctor_get(v___x_1982_, 1);
v_zetaDeltaFVarIds_1985_ = lean_ctor_get(v___x_1982_, 2);
v_postponed_1986_ = lean_ctor_get(v___x_1982_, 3);
v_diag_1987_ = lean_ctor_get(v___x_1982_, 4);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1989_ = v___x_1982_;
v_isShared_1990_ = v_isSharedCheck_2016_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_diag_1987_);
lean_inc(v_postponed_1986_);
lean_inc(v_zetaDeltaFVarIds_1985_);
lean_inc(v_cache_1984_);
lean_inc(v_mctx_1983_);
lean_dec(v___x_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2016_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_depth_1991_; lean_object* v_levelAssignDepth_1992_; lean_object* v_lmvarCounter_1993_; lean_object* v_mvarCounter_1994_; lean_object* v_lDecls_1995_; lean_object* v_decls_1996_; lean_object* v_userNames_1997_; lean_object* v_lAssignment_1998_; lean_object* v_eAssignment_1999_; lean_object* v_dAssignment_2000_; lean_object* v_instanceTypedMVars_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2015_; 
v_depth_1991_ = lean_ctor_get(v_mctx_1983_, 0);
v_levelAssignDepth_1992_ = lean_ctor_get(v_mctx_1983_, 1);
v_lmvarCounter_1993_ = lean_ctor_get(v_mctx_1983_, 2);
v_mvarCounter_1994_ = lean_ctor_get(v_mctx_1983_, 3);
v_lDecls_1995_ = lean_ctor_get(v_mctx_1983_, 4);
v_decls_1996_ = lean_ctor_get(v_mctx_1983_, 5);
v_userNames_1997_ = lean_ctor_get(v_mctx_1983_, 6);
v_lAssignment_1998_ = lean_ctor_get(v_mctx_1983_, 7);
v_eAssignment_1999_ = lean_ctor_get(v_mctx_1983_, 8);
v_dAssignment_2000_ = lean_ctor_get(v_mctx_1983_, 9);
v_instanceTypedMVars_2001_ = lean_ctor_get(v_mctx_1983_, 10);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_mctx_1983_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2003_ = v_mctx_1983_;
v_isShared_2004_ = v_isSharedCheck_2015_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_instanceTypedMVars_2001_);
lean_inc(v_dAssignment_2000_);
lean_inc(v_eAssignment_1999_);
lean_inc(v_lAssignment_1998_);
lean_inc(v_userNames_1997_);
lean_inc(v_decls_1996_);
lean_inc(v_lDecls_1995_);
lean_inc(v_mvarCounter_1994_);
lean_inc(v_lmvarCounter_1993_);
lean_inc(v_levelAssignDepth_1992_);
lean_inc(v_depth_1991_);
lean_dec(v_mctx_1983_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2015_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = lean_box(0);
v___x_2006_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1999_, v_mvarId_1978_, v_val_1979_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 8, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_depth_1991_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_levelAssignDepth_1992_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_lmvarCounter_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_mvarCounter_1994_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_lDecls_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_decls_1996_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_userNames_1997_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_lAssignment_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 9, v_dAssignment_2000_);
lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_instanceTypedMVars_2001_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2008_);
v___x_2010_ = v___x_1989_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_cache_1984_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_zetaDeltaFVarIds_1985_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_postponed_1986_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_diag_1987_);
v___x_2010_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_st_ref_put(v___y_1980_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2005_);
return v___x_2012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_2017_, lean_object* v_val_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_2017_, v_val_2018_, v___y_2019_);
lean_dec(v___y_2019_);
return v_res_2021_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_14983__overap_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_14983__overap_2032_ = lean_panic_fn_borrowed(v___x_2031_, v_msg_2023_);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
v___x_2033_ = lean_apply_7(v___x_14983__overap_2032_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, lean_box(0));
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_2043_, size_t v_i_2044_, size_t v_stop_2045_, lean_object* v_b_2046_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_eq(v_i_2044_, v_stop_2045_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; 
v___x_2048_ = lean_array_uget_borrowed(v_as_2043_, v_i_2044_);
v_fst_2049_ = lean_ctor_get(v___x_2048_, 0);
v_snd_2050_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2050_);
v___x_2051_ = l_Lean_mkFVar(v_snd_2050_);
lean_inc(v_fst_2049_);
v___x_2052_ = l_Lean_Meta_FVarSubst_insert(v_b_2046_, v_fst_2049_, v___x_2051_);
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2044_, v___x_2053_);
v_i_2044_ = v___x_2054_;
v_b_2046_ = v___x_2052_;
goto _start;
}
else
{
return v_b_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_2056_, lean_object* v_i_2057_, lean_object* v_stop_2058_, lean_object* v_b_2059_){
_start:
{
size_t v_i_boxed_2060_; size_t v_stop_boxed_2061_; lean_object* v_res_2062_; 
v_i_boxed_2060_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_stop_boxed_2061_ = lean_unbox_usize(v_stop_2058_);
lean_dec(v_stop_2058_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_2056_, v_i_boxed_2060_, v_stop_boxed_2061_, v_b_2059_);
lean_dec_ref(v_as_2056_);
return v_res_2062_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2063_; lean_object* v_dummy_2064_; 
v___x_2063_ = lean_box(0);
v_dummy_2064_ = l_Lean_Expr_sort___override(v___x_2063_);
return v_dummy_2064_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2069_ = lean_unsigned_to_nat(62u);
v___x_2070_ = lean_unsigned_to_nat(323u);
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2073_ = l_mkPanicMessageWithDecl(v___x_2072_, v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v_snd_2076_, lean_object* v___x_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, lean_object* v_e_2080_, lean_object* v___x_2081_, lean_object* v_head_2082_, lean_object* v_fst_2083_, lean_object* v_tail_2084_, uint8_t v___x_2085_, lean_object* v_snd_2086_, lean_object* v___x_2087_, lean_object* v_fs_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_getElimInfo(v___x_2074_, v___x_2075_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
lean_inc(v_snd_2076_);
v___x_2098_ = l_Lean_MVarId_getTag(v_snd_2076_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
lean_inc(v_a_2097_);
v___x_2100_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_2097_, v___x_2077_, v_a_2099_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v_elimApp_2102_; lean_object* v_alts_2103_; lean_object* v_motivePos_2104_; lean_object* v_nargs_2105_; lean_object* v_dummy_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v_elimApp_2102_ = lean_ctor_get(v_a_2101_, 0);
lean_inc_ref_n(v_elimApp_2102_, 2);
v_alts_2103_ = lean_ctor_get(v_a_2101_, 3);
lean_inc_ref(v_alts_2103_);
lean_dec(v_a_2101_);
v_motivePos_2104_ = lean_ctor_get(v_a_2097_, 2);
lean_inc(v_motivePos_2104_);
lean_dec(v_a_2097_);
v_nargs_2105_ = l_Lean_Expr_getAppNumArgs(v_elimApp_2102_);
v_dummy_2106_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0);
lean_inc(v_nargs_2105_);
v___x_2107_ = lean_mk_array(v_nargs_2105_, v_dummy_2106_);
v___x_2108_ = lean_nat_sub(v_nargs_2105_, v___x_2078_);
lean_dec(v_nargs_2105_);
v___x_2109_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_2102_, v___x_2107_, v___x_2108_);
v___x_2110_ = lean_array_get(v___x_2079_, v___x_2109_, v_motivePos_2104_);
lean_dec(v_motivePos_2104_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l_Lean_Expr_mvarId_x21(v___x_2110_);
lean_dec(v___x_2110_);
v___x_2112_ = l_Lean_Expr_fvarId_x21(v_e_2080_);
v___x_2113_ = lean_mk_empty_array_with_capacity(v___x_2078_);
lean_inc_ref(v___x_2113_);
v___x_2114_ = lean_array_push(v___x_2113_, v___x_2112_);
v___x_2115_ = lean_mk_empty_array_with_capacity(v___x_2081_);
lean_inc(v_snd_2076_);
v___x_2116_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_2076_, v___x_2111_, v___x_2114_, v___x_2115_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2116_, 1);
v___x_2117_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_2076_, v_elimApp_2102_, v___y_2092_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = lean_array_get_size(v_alts_2103_);
v___x_2119_ = lean_nat_dec_eq(v___x_2118_, v___x_2078_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_alts_2103_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
v___x_2120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4);
v___x_2121_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2120_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v_name_2123_; lean_object* v_mvarId_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2196_; 
v___x_2122_ = lean_array_fget(v_alts_2103_, v___x_2081_);
lean_dec_ref(v_alts_2103_);
v_name_2123_ = lean_ctor_get(v___x_2122_, 0);
v_mvarId_2124_ = lean_ctor_get(v___x_2122_, 2);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2122_, 1);
lean_dec(v_unused_2197_);
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2196_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_mvarId_2124_);
lean_inc(v_name_2123_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2196_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_MVarId_intro(v_mvarId_2124_, v_head_2082_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v_fst_2130_; lean_object* v_snd_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2187_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v_fst_2130_ = lean_ctor_get(v_a_2129_, 0);
v_snd_2131_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2133_ = v_a_2129_;
v_isShared_2134_ = v_isSharedCheck_2187_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_snd_2131_);
lean_inc(v_fst_2130_);
lean_dec(v_a_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2187_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_array_get_size(v_fst_2083_);
v___x_2136_ = l_Lean_Meta_introNCore(v_snd_2131_, v___x_2135_, v_tail_2084_, v___x_2085_, v___x_2119_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2178_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2178_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2178_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2177_; 
v_fst_2141_ = lean_ctor_get(v_a_2137_, 0);
v_snd_2142_ = lean_ctor_get(v_a_2137_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_a_2137_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2144_ = v_a_2137_;
v_isShared_2145_ = v_isSharedCheck_2177_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_snd_2142_);
lean_inc(v_fst_2141_);
lean_dec(v_a_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2177_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___y_2147_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2167_ = l_Array_zip___redArg(v_fst_2083_, v_fst_2141_);
lean_dec(v_fst_2141_);
v___x_2168_ = lean_array_get_size(v___x_2167_);
v___x_2169_ = lean_nat_dec_lt(v___x_2081_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_dec_ref(v___x_2167_);
v___y_2147_ = v_fs_2088_;
goto v___jp_2146_;
}
else
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_nat_dec_le(v___x_2168_, v___x_2168_);
if (v___x_2170_ == 0)
{
if (v___x_2169_ == 0)
{
lean_dec_ref(v___x_2167_);
v___y_2147_ = v_fs_2088_;
goto v___jp_2146_;
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2168_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2167_, v___x_2171_, v___x_2172_, v_fs_2088_);
lean_dec_ref(v___x_2167_);
v___y_2147_ = v___x_2173_;
goto v___jp_2146_;
}
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2168_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2167_, v___x_2174_, v___x_2175_, v_fs_2088_);
lean_dec_ref(v___x_2167_);
v___y_2147_ = v___x_2176_;
goto v___jp_2146_;
}
}
v___jp_2146_:
{
lean_object* v___x_2149_; 
lean_inc(v_name_2123_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v_snd_2086_);
lean_ctor_set(v___x_2144_, 0, v_name_2123_);
v___x_2149_ = v___x_2144_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_name_2123_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_snd_2086_);
v___x_2149_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_mkFVar(v_fst_2130_);
v___x_2153_ = lean_array_push(v___x_2087_, v___x_2152_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 2, v___y_2147_);
lean_ctor_set(v___x_2126_, 1, v___x_2153_);
lean_ctor_set(v___x_2126_, 0, v_snd_2142_);
v___x_2155_ = v___x_2126_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_snd_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v___y_2147_);
v___x_2155_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_name_2123_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_array_push(v___x_2113_, v___x_2157_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2158_);
lean_ctor_set(v___x_2133_, 0, v___x_2151_);
v___x_2160_ = v___x_2133_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2160_);
v___x_2162_ = v___x_2139_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
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
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_del_object(v___x_2133_);
lean_dec(v_fst_2130_);
lean_del_object(v___x_2126_);
lean_dec(v_name_2123_);
lean_dec_ref(v___x_2113_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
v_a_2179_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2136_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2136_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_del_object(v___x_2126_);
lean_dec(v_name_2123_);
lean_dec_ref(v___x_2113_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
v_a_2188_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2128_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2128_);
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
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_alts_2103_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
v_a_2198_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2117_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2117_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_alts_2103_);
lean_dec_ref(v_elimApp_2102_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec(v_snd_2076_);
v_a_2206_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2116_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2116_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2097_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec(v_snd_2076_);
v_a_2214_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2100_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2100_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2097_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec_ref(v___x_2077_);
lean_dec(v_snd_2076_);
v_a_2222_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2098_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2098_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
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
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec_ref(v___x_2077_);
lean_dec(v_snd_2076_);
v_a_2230_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2096_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2096_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2238_ = _args[0];
lean_object* v___x_2239_ = _args[1];
lean_object* v_snd_2240_ = _args[2];
lean_object* v___x_2241_ = _args[3];
lean_object* v___x_2242_ = _args[4];
lean_object* v___x_2243_ = _args[5];
lean_object* v_e_2244_ = _args[6];
lean_object* v___x_2245_ = _args[7];
lean_object* v_head_2246_ = _args[8];
lean_object* v_fst_2247_ = _args[9];
lean_object* v_tail_2248_ = _args[10];
lean_object* v___x_2249_ = _args[11];
lean_object* v_snd_2250_ = _args[12];
lean_object* v___x_2251_ = _args[13];
lean_object* v_fs_2252_ = _args[14];
lean_object* v___y_2253_ = _args[15];
lean_object* v___y_2254_ = _args[16];
lean_object* v___y_2255_ = _args[17];
lean_object* v___y_2256_ = _args[18];
lean_object* v___y_2257_ = _args[19];
lean_object* v___y_2258_ = _args[20];
lean_object* v___y_2259_ = _args[21];
_start:
{
uint8_t v___x_19079__boxed_2260_; lean_object* v_res_2261_; 
v___x_19079__boxed_2260_ = lean_unbox(v___x_2249_);
v_res_2261_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v___x_2238_, v___x_2239_, v_snd_2240_, v___x_2241_, v___x_2242_, v___x_2243_, v_e_2244_, v___x_2245_, v_head_2246_, v_fst_2247_, v_tail_2248_, v___x_19079__boxed_2260_, v_snd_2250_, v___x_2251_, v_fs_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_fst_2247_);
lean_dec(v___x_2245_);
lean_dec_ref(v_e_2244_);
lean_dec_ref(v___x_2243_);
lean_dec(v___x_2242_);
return v_res_2261_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2263_ = lean_unsigned_to_nat(76u);
v___x_2264_ = lean_unsigned_to_nat(315u);
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2267_ = l_mkPanicMessageWithDecl(v___x_2266_, v___x_2265_, v___x_2264_, v___x_2263_, v___x_2262_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(uint8_t v___x_2275_, lean_object* v_e_2276_, lean_object* v___x_2277_, lean_object* v_g_2278_, lean_object* v___x_2279_, lean_object* v_fs_2280_, lean_object* v_pat_2281_, lean_object* v_____r_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___y_2294_; uint8_t v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2338_; lean_object* v___x_2344_; 
v___x_2344_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2281_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2338_ = v___x_2345_;
goto v___jp_2337_;
}
else
{
lean_object* v_head_2346_; 
v_head_2346_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_head_2346_);
lean_dec_ref_known(v___x_2344_, 2);
v___y_2338_ = v_head_2346_;
goto v___jp_2337_;
}
v___jp_2290_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
v___x_2292_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2291_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2292_;
}
v___jp_2293_:
{
uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_fst_2305_; 
v___x_2297_ = 0;
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2300_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1, v___x_2297_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 1, v___x_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 2, v___x_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 3, v___x_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 4, v___x_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 5, v___x_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1 + 6, v___x_2275_);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
lean_inc_ref(v___x_2302_);
v___x_2303_ = lean_array_push(v___x_2302_, v___x_2300_);
v___x_2304_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2296_, v___x_2303_, v___y_2295_, v___x_2298_, v___y_2294_);
lean_dec_ref(v___x_2303_);
v_fst_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_fst_2305_);
if (lean_obj_tag(v_fst_2305_) == 1)
{
lean_object* v_tail_2306_; 
v_tail_2306_ = lean_ctor_get(v_fst_2305_, 1);
lean_inc(v_tail_2306_);
if (lean_obj_tag(v_tail_2306_) == 0)
{
lean_object* v_snd_2307_; lean_object* v_head_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_snd_2307_ = lean_ctor_get(v___x_2304_, 1);
lean_inc(v_snd_2307_);
lean_dec_ref(v___x_2304_);
v_head_2308_ = lean_ctor_get(v_fst_2305_, 0);
lean_inc(v_head_2308_);
lean_dec_ref_known(v_fst_2305_, 2);
lean_inc_ref(v_e_2276_);
lean_inc_ref(v___x_2302_);
v___x_2309_ = lean_array_push(v___x_2302_, v_e_2276_);
v___x_2310_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2309_, v___x_2277_, v___x_2275_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = l_Lean_MVarId_revert(v_g_2278_, v_a_2311_, v___x_2275_, v___x_2275_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v_fst_2314_; lean_object* v_snd_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v_fst_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_fst_2314_);
v_snd_2315_ = lean_ctor_get(v_a_2313_, 1);
lean_inc_n(v_snd_2315_, 2);
lean_dec(v_a_2313_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4));
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_box(v___x_2275_);
v___f_2319_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed), 22, 15);
lean_closure_set(v___f_2319_, 0, v___x_2316_);
lean_closure_set(v___f_2319_, 1, v___x_2317_);
lean_closure_set(v___f_2319_, 2, v_snd_2315_);
lean_closure_set(v___f_2319_, 3, v___x_2309_);
lean_closure_set(v___f_2319_, 4, v___x_2301_);
lean_closure_set(v___f_2319_, 5, v___x_2279_);
lean_closure_set(v___f_2319_, 6, v_e_2276_);
lean_closure_set(v___f_2319_, 7, v___x_2298_);
lean_closure_set(v___f_2319_, 8, v_head_2308_);
lean_closure_set(v___f_2319_, 9, v_fst_2314_);
lean_closure_set(v___f_2319_, 10, v_tail_2306_);
lean_closure_set(v___f_2319_, 11, v___x_2318_);
lean_closure_set(v___f_2319_, 12, v_snd_2307_);
lean_closure_set(v___f_2319_, 13, v___x_2302_);
lean_closure_set(v___f_2319_, 14, v_fs_2280_);
v___x_2320_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2315_, v___f_2319_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2320_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v___x_2309_);
lean_dec(v_head_2308_);
lean_dec(v_snd_2307_);
lean_dec_ref(v___x_2302_);
lean_dec(v_fs_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v_e_2276_);
v_a_2321_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2312_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2312_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v___x_2309_);
lean_dec(v_head_2308_);
lean_dec(v_snd_2307_);
lean_dec_ref(v___x_2302_);
lean_dec(v_fs_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v_g_2278_);
lean_dec_ref(v_e_2276_);
v_a_2329_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2310_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2310_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_dec(v_tail_2306_);
lean_dec_ref_known(v_fst_2305_, 2);
lean_dec_ref(v___x_2304_);
lean_dec_ref(v___x_2302_);
lean_dec(v_fs_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v_g_2278_);
lean_dec(v___x_2277_);
lean_dec_ref(v_e_2276_);
goto v___jp_2290_;
}
}
else
{
lean_dec(v_fst_2305_);
lean_dec_ref(v___x_2304_);
lean_dec_ref(v___x_2302_);
lean_dec(v_fs_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v_g_2278_);
lean_dec(v___x_2277_);
lean_dec_ref(v_e_2276_);
goto v___jp_2290_;
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v_ref_2342_; uint8_t v___x_2343_; 
lean_inc_ref(v___y_2338_);
v___x_2339_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2338_);
v_fst_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_fst_2340_);
v_snd_2341_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v___x_2339_);
v_ref_2342_ = lean_ctor_get(v___y_2338_, 0);
lean_inc(v_ref_2342_);
lean_dec_ref(v___y_2338_);
v___x_2343_ = lean_unbox(v_fst_2340_);
lean_dec(v_fst_2340_);
v___y_2294_ = v_snd_2341_;
v___y_2295_ = v___x_2343_;
v___y_2296_ = v_ref_2342_;
goto v___jp_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object* v___x_2347_, lean_object* v_e_2348_, lean_object* v___x_2349_, lean_object* v_g_2350_, lean_object* v___x_2351_, lean_object* v_fs_2352_, lean_object* v_pat_2353_, lean_object* v_____r_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
uint8_t v___x_19451__boxed_2362_; lean_object* v_res_2363_; 
v___x_19451__boxed_2362_ = lean_unbox(v___x_2347_);
v_res_2363_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_19451__boxed_2362_, v_e_2348_, v___x_2349_, v_g_2350_, v___x_2351_, v_fs_2352_, v_pat_2353_, v_____r_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2364_, lean_object* v_cont_2365_, lean_object* v_g_2366_, lean_object* v_fs_2367_, lean_object* v_clears_2368_, lean_object* v_a_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2364_, v_cont_2365_, v_g_2366_, v_fs_2367_, v_clears_2368_, v_a_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2379_, lean_object* v_g_2380_, lean_object* v_fs_2381_, lean_object* v_clears_2382_, lean_object* v_a_2383_, lean_object* v_cont_2384_, lean_object* v_ref_2385_, lean_object* v_p_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2394_ = lean_box(0);
lean_inc_ref(v_e_2379_);
v___x_2395_ = l_Lean_Expr_mdata___override(v___x_2394_, v_e_2379_);
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_box(0);
v___x_2398_ = 0;
v___x_2399_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2385_, v___x_2395_, v___x_2396_, v___x_2396_, v___x_2397_, v___x_2398_, v___x_2398_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2400_; 
lean_dec_ref_known(v___x_2399_, 1);
v___x_2400_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2380_, v_fs_2381_, v_clears_2382_, v_e_2379_, v_a_2383_, v_p_2386_, v_cont_2384_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec_ref(v_e_2379_);
return v___x_2400_;
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_p_2386_);
lean_dec_ref(v_cont_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_clears_2382_);
lean_dec(v_fs_2381_);
lean_dec(v_g_2380_);
lean_dec_ref(v_e_2379_);
v_a_2401_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2409_, lean_object* v_g_2410_, lean_object* v_fs_2411_, lean_object* v_clears_2412_, lean_object* v_a_2413_, lean_object* v_cont_2414_, lean_object* v_ref_2415_, lean_object* v_p_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2409_, v_g_2410_, v_fs_2411_, v_clears_2412_, v_a_2413_, v_cont_2414_, v_ref_2415_, v_p_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2425_, lean_object* v_clears_2426_, lean_object* v_cont_2427_, lean_object* v_a_2428_, lean_object* v_goal_2429_, lean_object* v_ctorName_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_goal_2429_);
lean_dec_ref(v_cont_2427_);
lean_dec_ref(v_clears_2426_);
lean_dec(v_fs_2425_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v_a_2431_);
lean_ctor_set(v___x_2439_, 1, v_a_2428_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v_head_2441_; lean_object* v_tail_2442_; lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2477_; 
v_head_2441_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_head_2441_);
v_tail_2442_ = lean_ctor_get(v_a_2431_, 1);
lean_inc(v_tail_2442_);
lean_dec_ref_known(v_a_2431_, 2);
v_fst_2443_ = lean_ctor_get(v_head_2441_, 0);
v_snd_2444_ = lean_ctor_get(v_head_2441_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_head_2441_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2446_ = v_head_2441_;
v_isShared_2447_ = v_isSharedCheck_2477_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_snd_2444_);
lean_inc(v_fst_2443_);
lean_dec(v_head_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2477_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_fst_2443_);
v___x_2449_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2448_, v_ctorName_2430_);
lean_dec_ref_known(v___x_2448_, 1);
if (v___x_2449_ == 0)
{
lean_del_object(v___x_2446_);
lean_dec(v_snd_2444_);
v_a_2431_ = v_tail_2442_;
goto _start;
}
else
{
lean_object* v_mvarId_2451_; lean_object* v_fields_2452_; lean_object* v_subst_2453_; lean_object* v_fs_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_mvarId_2451_ = lean_ctor_get(v_goal_2429_, 0);
lean_inc(v_mvarId_2451_);
v_fields_2452_ = lean_ctor_get(v_goal_2429_, 1);
lean_inc_ref(v_fields_2452_);
v_subst_2453_ = lean_ctor_get(v_goal_2429_, 2);
lean_inc(v_subst_2453_);
lean_dec_ref(v_goal_2429_);
v_fs_2454_ = l_Lean_Meta_FVarSubst_append(v_fs_2425_, v_subst_2453_);
v___x_2455_ = lean_array_to_list(v_fields_2452_);
v___x_2456_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_snd_2444_, v___x_2455_);
v___x_2457_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2451_, v_fs_2454_, v_clears_2426_, v_a_2428_, v___x_2456_, v_cont_2427_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2468_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v_a_2458_);
lean_ctor_set(v___x_2446_, 0, v_tail_2442_);
v___x_2463_ = v___x_2446_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_tail_2442_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2465_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2463_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_del_object(v___x_2446_);
lean_dec(v_tail_2442_);
v_a_2469_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2457_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2457_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2478_, lean_object* v_clears_2479_, lean_object* v_cont_2480_, lean_object* v_as_2481_, size_t v_i_2482_, size_t v_stop_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_usize_dec_eq(v_i_2482_, v_stop_2483_);
if (v___x_2492_ == 0)
{
lean_object* v_fst_2493_; lean_object* v_snd_2494_; lean_object* v___x_2495_; lean_object* v_toInductionSubgoal_2496_; lean_object* v_ctorName_2497_; lean_object* v___x_2498_; 
v_fst_2493_ = lean_ctor_get(v_b_2484_, 0);
lean_inc(v_fst_2493_);
v_snd_2494_ = lean_ctor_get(v_b_2484_, 1);
lean_inc(v_snd_2494_);
lean_dec_ref(v_b_2484_);
v___x_2495_ = lean_array_uget_borrowed(v_as_2481_, v_i_2482_);
v_toInductionSubgoal_2496_ = lean_ctor_get(v___x_2495_, 0);
v_ctorName_2497_ = lean_ctor_get(v___x_2495_, 1);
lean_inc_ref(v_toInductionSubgoal_2496_);
lean_inc_ref(v_cont_2480_);
lean_inc_ref(v_clears_2479_);
lean_inc(v_fs_2478_);
v___x_2498_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2478_, v_clears_2479_, v_cont_2480_, v_snd_2494_, v_toInductionSubgoal_2496_, v_ctorName_2497_, v_fst_2493_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; size_t v___x_2500_; size_t v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2482_, v___x_2500_);
v_i_2482_ = v___x_2501_;
v_b_2484_ = v_a_2499_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2480_);
lean_dec_ref(v_clears_2479_);
lean_dec(v_fs_2478_);
return v___x_2498_;
}
}
else
{
lean_object* v___x_2503_; 
lean_dec_ref(v_cont_2480_);
lean_dec_ref(v_clears_2479_);
lean_dec(v_fs_2478_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_b_2484_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_a_2506_, lean_object* v_fs_2507_, lean_object* v_clears_2508_, lean_object* v_cont_2509_, lean_object* v_e_2510_, lean_object* v___x_2511_, lean_object* v_g_2512_, lean_object* v___x_2513_, lean_object* v_pat_2514_, lean_object* v___y_2515_, lean_object* v_asFVar_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___y_2526_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___y_2561_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2573_ = lean_box(0);
lean_inc_ref(v_e_2510_);
v___x_2574_ = l_Lean_Expr_mdata___override(v___x_2573_, v_e_2510_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_box(0);
v___x_2577_ = 0;
lean_inc(v___y_2515_);
v___x_2578_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2515_, v___x_2574_, v___x_2575_, v___x_2575_, v___x_2576_, v___x_2577_, v___x_2577_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2578_, 1);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc_ref(v_e_2510_);
v___x_2579_ = lean_apply_6(v_asFVar_2516_, v_e_2510_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, lean_box(0));
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; 
lean_dec_ref_known(v___x_2579_, 1);
v___x_2580_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2577_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2580_, 1);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc_ref(v_e_2510_);
v___x_2581_ = lean_infer_type(v_e_2510_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l_Lean_Meta_whnfD(v_a_2582_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = l_Lean_Expr_getAppFn(v_a_2584_);
if (lean_obj_tag(v___x_2585_) == 4)
{
lean_object* v_declName_2586_; lean_object* v___x_2587_; lean_object* v_env_2588_; lean_object* v___x_2589_; 
v_declName_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_declName_2586_);
lean_dec_ref_known(v___x_2585_, 2);
v___x_2587_ = lean_st_ref_get(v___y_2523_);
v_env_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc_ref(v_env_2588_);
lean_dec(v___x_2587_);
v___x_2589_ = l_Lean_Environment_find_x3f(v_env_2588_, v_declName_2586_, v___x_2577_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2510_, v_a_2584_, lean_box(0), v___x_2590_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2591_;
goto v___jp_2560_;
}
else
{
lean_object* v_val_2592_; 
v_val_2592_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v___x_2589_, 1);
switch(lean_obj_tag(v_val_2592_))
{
case 4:
{
lean_object* v_val_2593_; uint8_t v_kind_2594_; 
lean_dec(v___y_2515_);
v_val_2593_ = lean_ctor_get(v_val_2592_, 0);
lean_inc_ref(v_val_2593_);
lean_dec_ref_known(v_val_2592_, 1);
v_kind_2594_ = lean_ctor_get_uint8(v_val_2593_, sizeof(void*)*1);
lean_dec_ref(v_val_2593_);
if (v_kind_2594_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v_a_2584_);
v___x_2595_ = lean_box(0);
lean_inc(v_fs_2507_);
v___x_2596_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2577_, v_e_2510_, v___x_2511_, v_g_2512_, v___x_2513_, v_fs_2507_, v_pat_2514_, v___x_2595_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2596_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_box(0);
lean_inc_ref(v_e_2510_);
v___x_2598_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2510_, v_a_2584_, lean_box(0), v___x_2597_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
lean_inc(v_fs_2507_);
v___x_2600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2577_, v_e_2510_, v___x_2511_, v_g_2512_, v___x_2513_, v_fs_2507_, v_pat_2514_, v_a_2599_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2600_;
goto v___jp_2560_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2601_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2598_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2598_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
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
}
case 5:
{
lean_object* v_val_2609_; lean_object* v_numParams_2610_; lean_object* v_ctors_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec(v_a_2584_);
lean_dec_ref(v___x_2513_);
lean_dec(v___x_2511_);
v_val_2609_ = lean_ctor_get(v_val_2592_, 0);
lean_inc_ref(v_val_2609_);
lean_dec_ref_known(v_val_2592_, 1);
v_numParams_2610_ = lean_ctor_get(v_val_2609_, 1);
lean_inc(v_numParams_2610_);
v_ctors_2611_ = lean_ctor_get(v_val_2609_, 4);
lean_inc(v_ctors_2611_);
lean_dec_ref(v_val_2609_);
v___x_2612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2613_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2514_);
v___x_2614_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2515_, v_numParams_2610_, v___x_2612_, v_ctors_2611_, v___x_2613_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v_numParams_2610_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_fst_2616_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_a_2615_, 1);
lean_inc(v_snd_2617_);
lean_dec(v_a_2615_);
v___x_2618_ = l_Lean_Expr_fvarId_x21(v_e_2510_);
lean_dec_ref(v_e_2510_);
v___x_2619_ = 1;
v___x_2620_ = l_Lean_MVarId_cases(v_g_2512_, v___x_2618_, v_fst_2616_, v___x_2619_, v___x_2575_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v_fst_2545_ = v_snd_2617_;
v_snd_2546_ = v_a_2621_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_snd_2617_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2622_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2620_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_g_2512_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2630_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2614_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2614_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
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
default: 
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v_val_2592_);
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
v___x_2638_ = lean_box(0);
v___x_2639_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2510_, v_a_2584_, lean_box(0), v___x_2638_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2639_;
goto v___jp_2560_;
}
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v___x_2585_);
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
v___x_2640_ = lean_box(0);
v___x_2641_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2510_, v_a_2584_, lean_box(0), v___x_2640_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2641_;
goto v___jp_2560_;
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2642_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2583_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2583_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2650_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2581_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2581_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2658_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2580_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2580_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2666_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2579_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2579_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v_asFVar_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v_pat_2514_);
lean_dec_ref(v___x_2513_);
lean_dec(v_g_2512_);
lean_dec(v___x_2511_);
lean_dec_ref(v_e_2510_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2674_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2578_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2578_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
v___jp_2525_:
{
if (lean_obj_tag(v___y_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2535_; 
v_a_2527_ = lean_ctor_get(v___y_2526_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___y_2526_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2529_ = v___y_2526_;
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___y_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_snd_2531_; lean_object* v___x_2533_; 
v_snd_2531_ = lean_ctor_get(v_a_2527_, 1);
lean_inc(v_snd_2531_);
lean_dec(v_a_2527_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_snd_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_snd_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2536_ = lean_ctor_get(v___y_2526_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___y_2526_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___y_2526_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___y_2526_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_array_get_size(v_snd_2546_);
v___x_2549_ = lean_nat_dec_lt(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref(v_snd_2546_);
lean_dec(v_fst_2545_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2506_);
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; uint8_t v___x_2552_; 
lean_inc(v_a_2506_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_fst_2545_);
lean_ctor_set(v___x_2551_, 1, v_a_2506_);
v___x_2552_ = lean_nat_dec_le(v___x_2548_, v___x_2548_);
if (v___x_2552_ == 0)
{
if (v___x_2549_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref_known(v___x_2551_, 2);
lean_dec_ref(v_snd_2546_);
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2506_);
return v___x_2553_;
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v_a_2506_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2548_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2507_, v_clears_2508_, v_cont_2509_, v_snd_2546_, v___x_2554_, v___x_2555_, v___x_2551_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v_snd_2546_);
v___y_2526_ = v___x_2556_;
goto v___jp_2525_;
}
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_a_2506_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2548_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2507_, v_clears_2508_, v_cont_2509_, v_snd_2546_, v___x_2557_, v___x_2558_, v___x_2551_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v_snd_2546_);
v___y_2526_ = v___x_2559_;
goto v___jp_2525_;
}
}
}
v___jp_2560_:
{
if (lean_obj_tag(v___y_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v_fst_2563_; lean_object* v_snd_2564_; 
v_a_2562_ = lean_ctor_get(v___y_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___y_2561_, 1);
v_fst_2563_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_fst_2563_);
v_snd_2564_ = lean_ctor_get(v_a_2562_, 1);
lean_inc(v_snd_2564_);
lean_dec(v_a_2562_);
v_fst_2545_ = v_fst_2563_;
v_snd_2546_ = v_snd_2564_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_cont_2509_);
lean_dec_ref(v_clears_2508_);
lean_dec(v_fs_2507_);
lean_dec(v_a_2506_);
v_a_2565_ = lean_ctor_get(v___y_2561_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___y_2561_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___y_2561_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___y_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_a_2682_ = _args[0];
lean_object* v_fs_2683_ = _args[1];
lean_object* v_clears_2684_ = _args[2];
lean_object* v_cont_2685_ = _args[3];
lean_object* v_e_2686_ = _args[4];
lean_object* v___x_2687_ = _args[5];
lean_object* v_g_2688_ = _args[6];
lean_object* v___x_2689_ = _args[7];
lean_object* v_pat_2690_ = _args[8];
lean_object* v___y_2691_ = _args[9];
lean_object* v_asFVar_2692_ = _args[10];
lean_object* v_x_2693_ = _args[11];
lean_object* v___y_2694_ = _args[12];
lean_object* v___y_2695_ = _args[13];
lean_object* v___y_2696_ = _args[14];
lean_object* v___y_2697_ = _args[15];
lean_object* v___y_2698_ = _args[16];
lean_object* v___y_2699_ = _args[17];
lean_object* v___y_2700_ = _args[18];
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_a_2682_, v_fs_2683_, v_clears_2684_, v_cont_2685_, v_e_2686_, v___x_2687_, v_g_2688_, v___x_2689_, v_pat_2690_, v___y_2691_, v_asFVar_2692_, v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_x_2693_);
return v_res_2701_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2706_ = l_Lean_MessageData_ofFormat(v___x_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2709_, lean_object* v___f_2710_, lean_object* v_e_2711_, lean_object* v_asFVar_2712_, lean_object* v_g_2713_, lean_object* v_fs_2714_, lean_object* v_cont_2715_, lean_object* v_clears_2716_, lean_object* v_a_2717_, lean_object* v___f_2718_, lean_object* v___f_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
switch(lean_obj_tag(v_pat_2709_))
{
case 1:
{
lean_object* v_a_2727_; 
lean_dec_ref(v___f_2719_);
lean_dec_ref(v___f_2718_);
v_a_2727_ = lean_ctor_get(v_pat_2709_, 1);
lean_inc(v_a_2727_);
if (lean_obj_tag(v_a_2727_) == 1)
{
lean_object* v_pre_2728_; 
v_pre_2728_ = lean_ctor_get(v_a_2727_, 0);
if (lean_obj_tag(v_pre_2728_) == 0)
{
lean_object* v_ref_2729_; lean_object* v_str_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_ref_2729_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2729_);
lean_dec_ref_known(v_pat_2709_, 2);
v_str_2730_ = lean_ctor_get(v_a_2727_, 1);
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2732_ = lean_string_dec_eq(v_str_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2733_ = lean_apply_9(v___f_2710_, v_ref_2729_, v_a_2727_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2733_;
}
else
{
uint8_t v___x_2734_; lean_object* v___x_2735_; 
lean_inc(v_pre_2728_);
lean_dec_ref_known(v_a_2727_, 2);
lean_dec_ref(v___f_2710_);
v___x_2734_ = 0;
v___x_2735_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2734_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec_ref_known(v___x_2735_, 1);
v___x_2736_ = lean_box(0);
lean_inc_ref(v_e_2711_);
v___x_2737_ = l_Lean_Expr_mdata___override(v___x_2736_, v_e_2711_);
v___x_2738_ = lean_box(0);
v___x_2739_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2729_, v___x_2737_, v___x_2738_, v___x_2738_, v_pre_2728_, v___x_2734_, v___x_2734_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; 
lean_dec_ref_known(v___x_2739_, 1);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
v___x_2740_ = lean_apply_6(v_asFVar_2712_, v_e_2711_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = l_Lean_Meta_substEq(v_g_2713_, v_a_2741_, v_fs_2714_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v_fst_2744_; lean_object* v_snd_2745_; lean_object* v___x_2746_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v_fst_2744_ = lean_ctor_get(v_a_2743_, 0);
lean_inc(v_fst_2744_);
v_snd_2745_ = lean_ctor_get(v_a_2743_, 1);
lean_inc(v_snd_2745_);
lean_dec(v_a_2743_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2746_ = lean_apply_11(v_cont_2715_, v_snd_2745_, v_fst_2744_, v_clears_2716_, v_a_2717_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2746_;
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
v_a_2747_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2742_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
v_a_2755_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2740_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2740_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
v_a_2763_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2739_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2739_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_ref_2729_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
v_a_2771_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2735_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2735_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
else
{
lean_object* v_ref_2779_; lean_object* v___x_2780_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
v_ref_2779_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2779_);
lean_dec_ref_known(v_pat_2709_, 2);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2780_ = lean_apply_9(v___f_2710_, v_ref_2779_, v_a_2727_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2780_;
}
}
else
{
lean_object* v_ref_2781_; lean_object* v___x_2782_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
v_ref_2781_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2781_);
lean_dec_ref_known(v_pat_2709_, 2);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2782_ = lean_apply_9(v___f_2710_, v_ref_2781_, v_a_2727_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2782_;
}
}
case 2:
{
lean_object* v_ref_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; 
lean_dec_ref(v___f_2719_);
lean_dec_ref(v___f_2718_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v___f_2710_);
v_ref_2783_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2783_);
lean_dec_ref_known(v_pat_2709_, 1);
v___x_2784_ = lean_box(0);
lean_inc_ref(v_e_2711_);
v___x_2785_ = l_Lean_Expr_mdata___override(v___x_2784_, v_e_2711_);
v___x_2786_ = lean_box(0);
v___x_2787_ = lean_box(0);
v___x_2788_ = 0;
v___x_2789_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2783_, v___x_2785_, v___x_2786_, v___x_2786_, v___x_2787_, v___x_2788_, v___x_2788_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref_known(v___x_2789_, 1);
if (lean_obj_tag(v_e_2711_) == 1)
{
lean_object* v_fvarId_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_fvarId_2790_ = lean_ctor_get(v_e_2711_, 0);
lean_inc(v_fvarId_2790_);
lean_dec_ref_known(v_e_2711_, 1);
v___x_2791_ = lean_array_push(v_clears_2716_, v_fvarId_2790_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2792_ = lean_apply_11(v_cont_2715_, v_g_2713_, v_fs_2714_, v___x_2791_, v_a_2717_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2792_;
}
else
{
lean_object* v___x_2793_; 
lean_dec_ref(v_e_2711_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2793_ = lean_apply_11(v_cont_2715_, v_g_2713_, v_fs_2714_, v_clears_2716_, v_a_2717_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2793_;
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2794_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2789_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2789_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
case 4:
{
lean_object* v_ref_2802_; lean_object* v_a_2803_; lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; 
lean_dec_ref(v___f_2719_);
lean_dec_ref(v___f_2718_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v___f_2710_);
v_ref_2802_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2802_);
v_a_2803_ = lean_ctor_get(v_pat_2709_, 1);
lean_inc_ref(v_a_2803_);
v_a_2804_ = lean_ctor_get(v_pat_2709_, 2);
lean_inc(v_a_2804_);
lean_dec_ref_known(v_pat_2709_, 3);
v___x_2805_ = lean_box(0);
lean_inc_ref(v_e_2711_);
v___x_2806_ = l_Lean_Expr_mdata___override(v___x_2805_, v_e_2711_);
v___x_2807_ = lean_box(0);
v___x_2808_ = lean_box(0);
v___x_2809_ = 0;
v___x_2810_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2802_, v___x_2806_, v___x_2807_, v___x_2807_, v___x_2808_, v___x_2809_, v___x_2809_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref_known(v___x_2810_, 1);
v___x_2811_ = l_Lean_Elab_Term_elabType(v_a_2804_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___x_2833_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc_ref(v_e_2711_);
v___x_2833_ = lean_infer_type(v_e_2711_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc_n(v_a_2834_, 2);
lean_dec_ref_known(v___x_2833_, 1);
lean_inc(v_a_2812_);
v___x_2835_ = l_Lean_Meta_isExprDefEq(v_a_2834_, v_a_2812_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; uint8_t v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = lean_unbox(v_a_2836_);
lean_dec(v_a_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2711_);
lean_inc(v_a_2812_);
v___x_2839_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2838_, v_a_2812_, v_a_2834_, v_e_2711_, v___x_2807_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_dec_ref_known(v___x_2839_, 1);
v___y_2814_ = v___y_2720_;
v___y_2815_ = v___y_2721_;
v___y_2816_ = v___y_2722_;
v___y_2817_ = v___y_2723_;
v___y_2818_ = v___y_2724_;
v___y_2819_ = v___y_2725_;
goto v___jp_2813_;
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_dec(v_a_2834_);
v___y_2814_ = v___y_2720_;
v___y_2815_ = v___y_2721_;
v___y_2816_ = v___y_2722_;
v___y_2817_ = v___y_2723_;
v___y_2818_ = v___y_2724_;
v___y_2819_ = v___y_2725_;
goto v___jp_2813_;
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2834_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2848_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2835_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2835_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2856_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2833_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2833_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
v___jp_2813_:
{
if (lean_obj_tag(v_e_2711_) == 1)
{
lean_object* v_fvarId_2820_; lean_object* v___x_2821_; 
v_fvarId_2820_ = lean_ctor_get(v_e_2711_, 0);
lean_inc(v_fvarId_2820_);
v___x_2821_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2713_, v_fvarId_2820_, v_a_2812_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2822_, v_fs_2714_, v_clears_2716_, v_e_2711_, v_a_2717_, v_a_2803_, v_cont_2715_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref_known(v_e_2711_, 1);
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref_known(v_e_2711_, 1);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
v_a_2824_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2821_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2821_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_a_2812_);
v___x_2832_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2713_, v_fs_2714_, v_clears_2716_, v_e_2711_, v_a_2717_, v_a_2803_, v_cont_2715_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v_e_2711_);
return v___x_2832_;
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2864_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2811_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2811_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_e_2711_);
v_a_2872_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2810_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2810_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
case 0:
{
lean_object* v_ref_2880_; lean_object* v_a_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v___f_2719_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
lean_dec_ref(v___f_2710_);
v_ref_2880_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2880_);
v_a_2881_ = lean_ctor_get(v_pat_2709_, 1);
lean_inc_ref(v_a_2881_);
lean_dec_ref_known(v_pat_2709_, 2);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2882_ = lean_apply_9(v___f_2718_, v_ref_2880_, v_a_2881_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2882_;
}
case 6:
{
lean_object* v_a_2883_; 
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
lean_dec_ref(v___f_2710_);
v_a_2883_ = lean_ctor_get(v_pat_2709_, 1);
if (lean_obj_tag(v_a_2883_) == 1)
{
lean_object* v_tail_2884_; 
v_tail_2884_ = lean_ctor_get(v_a_2883_, 1);
if (lean_obj_tag(v_tail_2884_) == 0)
{
lean_object* v_ref_2885_; lean_object* v_head_2886_; lean_object* v___x_2887_; 
lean_inc_ref(v_a_2883_);
lean_dec_ref(v___f_2719_);
v_ref_2885_ = lean_ctor_get(v_pat_2709_, 0);
lean_inc(v_ref_2885_);
lean_dec_ref_known(v_pat_2709_, 2);
v_head_2886_ = lean_ctor_get(v_a_2883_, 0);
lean_inc(v_head_2886_);
lean_dec_ref_known(v_a_2883_, 2);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2887_ = lean_apply_9(v___f_2718_, v_ref_2885_, v_head_2886_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; 
lean_dec_ref(v___f_2718_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2888_ = lean_apply_8(v___f_2719_, v_pat_2709_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2888_;
}
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref(v___f_2718_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2889_ = lean_apply_8(v___f_2719_, v_pat_2709_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2889_;
}
}
default: 
{
lean_object* v___x_2890_; 
lean_dec_ref(v___f_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_clears_2716_);
lean_dec_ref(v_cont_2715_);
lean_dec(v_fs_2714_);
lean_dec(v_g_2713_);
lean_dec_ref(v_asFVar_2712_);
lean_dec_ref(v_e_2711_);
lean_dec_ref(v___f_2710_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
v___x_2890_ = lean_apply_8(v___f_2719_, v_pat_2709_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, lean_box(0));
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2891_ = _args[0];
lean_object* v___f_2892_ = _args[1];
lean_object* v_e_2893_ = _args[2];
lean_object* v_asFVar_2894_ = _args[3];
lean_object* v_g_2895_ = _args[4];
lean_object* v_fs_2896_ = _args[5];
lean_object* v_cont_2897_ = _args[6];
lean_object* v_clears_2898_ = _args[7];
lean_object* v_a_2899_ = _args[8];
lean_object* v___f_2900_ = _args[9];
lean_object* v___f_2901_ = _args[10];
lean_object* v___y_2902_ = _args[11];
lean_object* v___y_2903_ = _args[12];
lean_object* v___y_2904_ = _args[13];
lean_object* v___y_2905_ = _args[14];
lean_object* v___y_2906_ = _args[15];
lean_object* v___y_2907_ = _args[16];
lean_object* v___y_2908_ = _args[17];
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2891_, v___f_2892_, v_e_2893_, v_asFVar_2894_, v_g_2895_, v_fs_2896_, v_cont_2897_, v_clears_2898_, v_a_2899_, v___f_2900_, v___f_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2910_, lean_object* v_fs_2911_, lean_object* v_clears_2912_, lean_object* v_e_2913_, lean_object* v_a_2914_, lean_object* v_pat_2915_, lean_object* v_cont_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_asFVar_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_e_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; lean_object* v___y_2931_; lean_object* v_ref_2943_; 
v_asFVar_2924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2925_ = lean_box(1);
v___x_2926_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2911_, 3);
v_e_2927_ = l_Lean_Meta_FVarSubst_apply(v_fs_2911_, v_e_2913_);
lean_inc_n(v_a_2914_, 2);
lean_inc_ref_n(v_clears_2912_, 2);
lean_inc_n(v_g_2910_, 2);
lean_inc_ref_n(v_cont_2916_, 2);
lean_inc_ref_n(v_e_2927_, 2);
v___f_2928_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2928_, 0, v_e_2927_);
lean_closure_set(v___f_2928_, 1, v_cont_2916_);
lean_closure_set(v___f_2928_, 2, v_g_2910_);
lean_closure_set(v___f_2928_, 3, v_fs_2911_);
lean_closure_set(v___f_2928_, 4, v_clears_2912_);
lean_closure_set(v___f_2928_, 5, v_a_2914_);
v___f_2929_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2929_, 0, v_e_2927_);
lean_closure_set(v___f_2929_, 1, v_g_2910_);
lean_closure_set(v___f_2929_, 2, v_fs_2911_);
lean_closure_set(v___f_2929_, 3, v_clears_2912_);
lean_closure_set(v___f_2929_, 4, v_a_2914_);
lean_closure_set(v___f_2929_, 5, v_cont_2916_);
v_ref_2943_ = lean_ctor_get(v_pat_2915_, 0);
lean_inc(v_ref_2943_);
v___y_2931_ = v_ref_2943_;
goto v___jp_2930_;
v___jp_2930_:
{
lean_object* v_toCold_2932_; lean_object* v_currRecDepth_2933_; lean_object* v_ref_2934_; uint16_t v_optionFlags_2935_; uint8_t v_suppressElabErrors_2936_; uint8_t v_isRecordingDeps_2937_; lean_object* v___f_2938_; lean_object* v___y_2939_; lean_object* v_ref_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_toCold_2932_ = lean_ctor_get(v_a_2921_, 0);
v_currRecDepth_2933_ = lean_ctor_get(v_a_2921_, 1);
v_ref_2934_ = lean_ctor_get(v_a_2921_, 2);
v_optionFlags_2935_ = lean_ctor_get_uint16(v_a_2921_, sizeof(void*)*3);
v_suppressElabErrors_2936_ = lean_ctor_get_uint8(v_a_2921_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2937_ = lean_ctor_get_uint8(v_a_2921_, sizeof(void*)*3 + 3);
lean_inc(v___y_2931_);
lean_inc_ref(v_pat_2915_);
lean_inc_n(v_g_2910_, 2);
lean_inc_ref(v_e_2927_);
lean_inc_ref(v_cont_2916_);
lean_inc_ref(v_clears_2912_);
lean_inc(v_fs_2911_);
lean_inc(v_a_2914_);
v___f_2938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2938_, 0, v_a_2914_);
lean_closure_set(v___f_2938_, 1, v_fs_2911_);
lean_closure_set(v___f_2938_, 2, v_clears_2912_);
lean_closure_set(v___f_2938_, 3, v_cont_2916_);
lean_closure_set(v___f_2938_, 4, v_e_2927_);
lean_closure_set(v___f_2938_, 5, v___x_2925_);
lean_closure_set(v___f_2938_, 6, v_g_2910_);
lean_closure_set(v___f_2938_, 7, v___x_2926_);
lean_closure_set(v___f_2938_, 8, v_pat_2915_);
lean_closure_set(v___f_2938_, 9, v___y_2931_);
lean_closure_set(v___f_2938_, 10, v_asFVar_2924_);
v___y_2939_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2939_, 0, v_pat_2915_);
lean_closure_set(v___y_2939_, 1, v___f_2928_);
lean_closure_set(v___y_2939_, 2, v_e_2927_);
lean_closure_set(v___y_2939_, 3, v_asFVar_2924_);
lean_closure_set(v___y_2939_, 4, v_g_2910_);
lean_closure_set(v___y_2939_, 5, v_fs_2911_);
lean_closure_set(v___y_2939_, 6, v_cont_2916_);
lean_closure_set(v___y_2939_, 7, v_clears_2912_);
lean_closure_set(v___y_2939_, 8, v_a_2914_);
lean_closure_set(v___y_2939_, 9, v___f_2929_);
lean_closure_set(v___y_2939_, 10, v___f_2938_);
v_ref_2940_ = l_Lean_replaceRef(v___y_2931_, v_ref_2934_);
lean_dec(v___y_2931_);
lean_inc(v_currRecDepth_2933_);
lean_inc_ref(v_toCold_2932_);
v___x_2941_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2941_, 0, v_toCold_2932_);
lean_ctor_set(v___x_2941_, 1, v_currRecDepth_2933_);
lean_ctor_set(v___x_2941_, 2, v_ref_2940_);
lean_ctor_set_uint16(v___x_2941_, sizeof(void*)*3, v_optionFlags_2935_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*3 + 2, v_suppressElabErrors_2936_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*3 + 3, v_isRecordingDeps_2937_);
v___x_2942_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2910_, v___y_2939_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v___x_2941_, v_a_2922_);
lean_dec_ref_known(v___x_2941_, 3);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2944_, lean_object* v_fs_2945_, lean_object* v_clears_2946_, lean_object* v_a_2947_, lean_object* v_pats_2948_, lean_object* v_cont_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
if (lean_obj_tag(v_pats_2948_) == 0)
{
lean_object* v___x_2957_; 
lean_inc(v_a_2955_);
lean_inc_ref(v_a_2954_);
lean_inc(v_a_2953_);
lean_inc_ref(v_a_2952_);
lean_inc(v_a_2951_);
lean_inc_ref(v_a_2950_);
v___x_2957_ = lean_apply_11(v_cont_2949_, v_g_2944_, v_fs_2945_, v_clears_2946_, v_a_2947_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, lean_box(0));
return v___x_2957_;
}
else
{
lean_object* v_head_2958_; lean_object* v_tail_2959_; lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; 
v_head_2958_ = lean_ctor_get(v_pats_2948_, 0);
lean_inc(v_head_2958_);
v_tail_2959_ = lean_ctor_get(v_pats_2948_, 1);
lean_inc(v_tail_2959_);
lean_dec_ref_known(v_pats_2948_, 2);
v_fst_2960_ = lean_ctor_get(v_head_2958_, 0);
lean_inc(v_fst_2960_);
v_snd_2961_ = lean_ctor_get(v_head_2958_, 1);
lean_inc(v_snd_2961_);
lean_dec(v_head_2958_);
v___f_2962_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2962_, 0, v_tail_2959_);
lean_closure_set(v___f_2962_, 1, v_cont_2949_);
v___x_2963_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2944_, v_fs_2945_, v_clears_2946_, v_snd_2961_, v_a_2947_, v_fst_2960_, v___f_2962_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_snd_2961_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2964_, lean_object* v_cont_2965_, lean_object* v_g_2966_, lean_object* v_fs_2967_, lean_object* v_clears_2968_, lean_object* v_a_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2966_, v_fs_2967_, v_clears_2968_, v_a_2969_, v_tail_2964_, v_cont_2965_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2978_, lean_object* v_fs_2979_, lean_object* v_clears_2980_, lean_object* v_a_2981_, lean_object* v_pats_2982_, lean_object* v_cont_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2978_, v_fs_2979_, v_clears_2980_, v_a_2981_, v_pats_2982_, v_cont_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_2992_, lean_object* v_clears_2993_, lean_object* v_cont_2994_, lean_object* v_as_2995_, lean_object* v_i_2996_, lean_object* v_stop_2997_, lean_object* v_b_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
size_t v_i_boxed_3006_; size_t v_stop_boxed_3007_; lean_object* v_res_3008_; 
v_i_boxed_3006_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_stop_boxed_3007_ = lean_unbox_usize(v_stop_2997_);
lean_dec(v_stop_2997_);
v_res_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2992_, v_clears_2993_, v_cont_2994_, v_as_2995_, v_i_boxed_3006_, v_stop_boxed_3007_, v_b_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_as_2995_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_3009_, lean_object* v_clears_3010_, lean_object* v_cont_3011_, lean_object* v_a_3012_, lean_object* v_goal_3013_, lean_object* v_ctorName_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3009_, v_clears_3010_, v_cont_3011_, v_a_3012_, v_goal_3013_, v_ctorName_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_ctorName_3014_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3024_, lean_object* v_fs_3025_, lean_object* v_clears_3026_, lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_pat_3029_, lean_object* v_cont_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3024_, v_fs_3025_, v_clears_3026_, v_e_3027_, v_a_3028_, v_pat_3029_, v_cont_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec_ref(v_e_3027_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3039_, lean_object* v_g_3040_, lean_object* v_fs_3041_, lean_object* v_clears_3042_, lean_object* v_a_3043_, lean_object* v_pats_3044_, lean_object* v_cont_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3040_, v_fs_3041_, v_clears_3042_, v_a_3043_, v_pats_3044_, v_cont_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_g_3055_, lean_object* v_fs_3056_, lean_object* v_clears_3057_, lean_object* v_a_3058_, lean_object* v_pats_3059_, lean_object* v_cont_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3054_, v_g_3055_, v_fs_3056_, v_clears_3057_, v_a_3058_, v_pats_3059_, v_cont_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3069_, lean_object* v_fs_3070_, lean_object* v_clears_3071_, lean_object* v_cont_3072_, lean_object* v_a_3073_, lean_object* v_goal_3074_, lean_object* v_ctorName_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3070_, v_clears_3071_, v_cont_3072_, v_a_3073_, v_goal_3074_, v_ctorName_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_fs_3086_, lean_object* v_clears_3087_, lean_object* v_cont_3088_, lean_object* v_a_3089_, lean_object* v_goal_3090_, lean_object* v_ctorName_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3085_, v_fs_3086_, v_clears_3087_, v_cont_3088_, v_a_3089_, v_goal_3090_, v_ctorName_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_ctorName_3091_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3101_, lean_object* v_mvarId_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3102_, v_x_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_mvarId_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3112_, v_mvarId_3113_, v_x_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3123_, lean_object* v_g_3124_, lean_object* v_fs_3125_, lean_object* v_clears_3126_, lean_object* v_e_3127_, lean_object* v_a_3128_, lean_object* v_pat_3129_, lean_object* v_cont_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3124_, v_fs_3125_, v_clears_3126_, v_e_3127_, v_a_3128_, v_pat_3129_, v_cont_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3139_, lean_object* v_g_3140_, lean_object* v_fs_3141_, lean_object* v_clears_3142_, lean_object* v_e_3143_, lean_object* v_a_3144_, lean_object* v_pat_3145_, lean_object* v_cont_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3139_, v_g_3140_, v_fs_3141_, v_clears_3142_, v_e_3143_, v_a_3144_, v_pat_3145_, v_cont_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v_e_3143_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3155_, lean_object* v_fs_3156_, lean_object* v_clears_3157_, lean_object* v_cont_3158_, lean_object* v_as_3159_, size_t v_i_3160_, size_t v_stop_3161_, lean_object* v_b_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3156_, v_clears_3157_, v_cont_3158_, v_as_3159_, v_i_3160_, v_stop_3161_, v_b_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3171_, lean_object* v_fs_3172_, lean_object* v_clears_3173_, lean_object* v_cont_3174_, lean_object* v_as_3175_, lean_object* v_i_3176_, lean_object* v_stop_3177_, lean_object* v_b_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
size_t v_i_boxed_3186_; size_t v_stop_boxed_3187_; lean_object* v_res_3188_; 
v_i_boxed_3186_ = lean_unbox_usize(v_i_3176_);
lean_dec(v_i_3176_);
v_stop_boxed_3187_ = lean_unbox_usize(v_stop_3177_);
lean_dec(v_stop_3177_);
v_res_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3171_, v_fs_3172_, v_clears_3173_, v_cont_3174_, v_as_3175_, v_i_boxed_3186_, v_stop_boxed_3187_, v_b_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec_ref(v_as_3175_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3189_, lean_object* v_val_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3189_, v_val_3190_, v___y_3194_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3199_, lean_object* v_val_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3199_, v_val_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3209_, lean_object* v_msg_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3219_, lean_object* v_msg_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3219_, v_msg_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3229_, lean_object* v_x_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3230_, v_x_3231_, v_x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3234_, lean_object* v_macroStack_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3234_, v_macroStack_3235_, v___y_3240_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3244_, lean_object* v_macroStack_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3244_, v_macroStack_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3254_, lean_object* v_x_3255_, size_t v_x_3256_, size_t v_x_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3255_, v_x_3256_, v_x_3257_, v_x_3258_, v_x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_, lean_object* v_x_3266_){
_start:
{
size_t v_x_20765__boxed_3267_; size_t v_x_20766__boxed_3268_; lean_object* v_res_3269_; 
v_x_20765__boxed_3267_ = lean_unbox_usize(v_x_3263_);
lean_dec(v_x_3263_);
v_x_20766__boxed_3268_ = lean_unbox_usize(v_x_3264_);
lean_dec(v_x_3264_);
v_res_3269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3261_, v_x_3262_, v_x_20765__boxed_3267_, v_x_20766__boxed_3268_, v_x_3265_, v_x_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3270_, lean_object* v_n_3271_, lean_object* v_k_3272_, lean_object* v_v_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3271_, v_k_3272_, v_v_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3275_, size_t v_depth_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_entries_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3276_, v_keys_3277_, v_vals_3278_, v_i_3280_, v_entries_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3283_, lean_object* v_depth_3284_, lean_object* v_keys_3285_, lean_object* v_vals_3286_, lean_object* v_heq_3287_, lean_object* v_i_3288_, lean_object* v_entries_3289_){
_start:
{
size_t v_depth_boxed_3290_; lean_object* v_res_3291_; 
v_depth_boxed_3290_ = lean_unbox_usize(v_depth_3284_);
lean_dec(v_depth_3284_);
v_res_3291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3283_, v_depth_boxed_3290_, v_keys_3285_, v_vals_3286_, v_heq_3287_, v_i_3288_, v_entries_3289_);
lean_dec_ref(v_vals_3286_);
lean_dec_ref(v_keys_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3293_, v_x_3294_, v_x_3295_, v_x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3298_, lean_object* v_as_3299_, size_t v_i_3300_, size_t v_stop_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_usize_dec_eq(v_i_3300_, v_stop_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = lean_array_uget_borrowed(v_as_3299_, v_i_3300_);
v___x_3304_ = l_Lean_instBEqFVarId_beq(v_a_3298_, v___x_3303_);
if (v___x_3304_ == 0)
{
size_t v___x_3305_; size_t v___x_3306_; 
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = lean_usize_add(v_i_3300_, v___x_3305_);
v_i_3300_ = v___x_3306_;
goto _start;
}
else
{
return v___x_3304_;
}
}
else
{
uint8_t v___x_3308_; 
v___x_3308_ = 0;
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3309_, lean_object* v_as_3310_, lean_object* v_i_3311_, lean_object* v_stop_3312_){
_start:
{
size_t v_i_boxed_3313_; size_t v_stop_boxed_3314_; uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_i_boxed_3313_ = lean_unbox_usize(v_i_3311_);
lean_dec(v_i_3311_);
v_stop_boxed_3314_ = lean_unbox_usize(v_stop_3312_);
lean_dec(v_stop_3312_);
v_res_3315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3309_, v_as_3310_, v_i_boxed_3313_, v_stop_boxed_3314_);
lean_dec_ref(v_as_3310_);
lean_dec(v_a_3309_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_array_get_size(v_as_3317_);
v___x_3321_ = lean_nat_dec_lt(v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
return v___x_3321_;
}
else
{
if (v___x_3321_ == 0)
{
return v___x_3321_;
}
else
{
size_t v___x_3322_; size_t v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___x_3320_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3318_, v_as_3317_, v___x_3322_, v___x_3323_);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3325_, lean_object* v_a_3326_){
_start:
{
uint8_t v_res_3327_; lean_object* v_r_3328_; 
v_res_3327_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3325_, v_a_3326_);
lean_dec(v_a_3326_);
lean_dec_ref(v_as_3325_);
v_r_3328_ = lean_box(v_res_3327_);
return v_r_3328_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3329_, lean_object* v___y_3330_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3329_, v___y_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec(v_snd_3332_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3336_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = 0;
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3338_);
lean_dec(v_x_3338_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_unsigned_to_nat(16u);
v___x_3344_ = lean_mk_array(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3348_, size_t v_sz_3349_, size_t v_i_3350_, lean_object* v_b_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = lean_usize_dec_lt(v_i_3350_, v_sz_3349_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3351_);
return v___x_3355_;
}
else
{
lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3487_; 
v_snd_3356_ = lean_ctor_get(v_b_3351_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_b_3351_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v_b_3351_, 0);
lean_dec(v_unused_3488_);
v___x_3358_ = v_b_3351_;
v_isShared_3359_ = v_isSharedCheck_3487_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_dec(v_b_3351_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3487_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v_a_3362_; lean_object* v_a_3369_; 
v___x_3360_ = lean_box(0);
v_a_3369_ = lean_array_uget_borrowed(v_as_3348_, v_i_3350_);
if (lean_obj_tag(v_a_3369_) == 0)
{
v_a_3362_ = v_snd_3356_;
goto v___jp_3361_;
}
else
{
lean_object* v_val_3370_; uint8_t v_a_3372_; lean_object* v___f_3375_; lean_object* v___f_3376_; 
v_val_3370_ = lean_ctor_get(v_a_3369_, 0);
v___f_3375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3356_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3376_, 0, v_snd_3356_);
if (lean_obj_tag(v_val_3370_) == 0)
{
lean_object* v_type_3377_; lean_object* v___x_3378_; uint8_t v_fst_3380_; lean_object* v_mctx_3381_; lean_object* v___y_3397_; lean_object* v_mctx_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_type_3377_ = lean_ctor_get(v_val_3370_, 3);
v___x_3378_ = lean_st_ref_get(v___y_3352_);
v_mctx_3402_ = lean_ctor_get(v___x_3378_, 0);
lean_inc_ref_n(v_mctx_3402_, 2);
lean_dec(v___x_3378_);
v___x_3403_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_mctx_3402_);
v___x_3405_ = l_Lean_Expr_hasFVar(v_type_3377_);
if (v___x_3405_ == 0)
{
uint8_t v___x_3406_; 
v___x_3406_ = l_Lean_Expr_hasMVar(v_type_3377_);
if (v___x_3406_ == 0)
{
lean_dec_ref_known(v___x_3404_, 2);
lean_dec_ref(v___f_3376_);
v_fst_3380_ = v___x_3406_;
v_mctx_3381_ = v_mctx_3402_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3407_; 
lean_dec_ref(v_mctx_3402_);
lean_inc_ref(v_type_3377_);
v___x_3407_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3377_, v___x_3404_);
v___y_3397_ = v___x_3407_;
goto v___jp_3396_;
}
}
else
{
lean_object* v___x_3408_; 
lean_dec_ref(v_mctx_3402_);
lean_inc_ref(v_type_3377_);
v___x_3408_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3377_, v___x_3404_);
v___y_3397_ = v___x_3408_;
goto v___jp_3396_;
}
v___jp_3379_:
{
lean_object* v___x_3382_; lean_object* v_cache_3383_; lean_object* v_zetaDeltaFVarIds_3384_; lean_object* v_postponed_3385_; lean_object* v_diag_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3394_; 
v___x_3382_ = lean_st_ref_take(v___y_3352_);
v_cache_3383_ = lean_ctor_get(v___x_3382_, 1);
v_zetaDeltaFVarIds_3384_ = lean_ctor_get(v___x_3382_, 2);
v_postponed_3385_ = lean_ctor_get(v___x_3382_, 3);
v_diag_3386_ = lean_ctor_get(v___x_3382_, 4);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3382_, 0);
lean_dec(v_unused_3395_);
v___x_3388_ = v___x_3382_;
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_diag_3386_);
lean_inc(v_postponed_3385_);
lean_inc(v_zetaDeltaFVarIds_3384_);
lean_inc(v_cache_3383_);
lean_dec(v___x_3382_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_mctx_3381_);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_mctx_3381_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_cache_3383_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_zetaDeltaFVarIds_3384_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_postponed_3385_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_diag_3386_);
v___x_3391_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_st_ref_put(v___y_3352_, v___x_3391_);
v_a_3372_ = v_fst_3380_;
goto v___jp_3371_;
}
}
}
v___jp_3396_:
{
lean_object* v_snd_3398_; lean_object* v_fst_3399_; lean_object* v_mctx_3400_; uint8_t v___x_3401_; 
v_snd_3398_ = lean_ctor_get(v___y_3397_, 1);
lean_inc(v_snd_3398_);
v_fst_3399_ = lean_ctor_get(v___y_3397_, 0);
lean_inc(v_fst_3399_);
lean_dec_ref(v___y_3397_);
v_mctx_3400_ = lean_ctor_get(v_snd_3398_, 1);
lean_inc_ref(v_mctx_3400_);
lean_dec(v_snd_3398_);
v___x_3401_ = lean_unbox(v_fst_3399_);
lean_dec(v_fst_3399_);
v_fst_3380_ = v___x_3401_;
v_mctx_3381_ = v_mctx_3400_;
goto v___jp_3379_;
}
}
else
{
uint8_t v_nondep_3409_; 
v_nondep_3409_ = lean_ctor_get_uint8(v_val_3370_, sizeof(void*)*5);
if (v_nondep_3409_ == 0)
{
lean_object* v_type_3410_; lean_object* v_value_3411_; lean_object* v___x_3412_; uint8_t v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___y_3432_; uint8_t v_fst_3437_; lean_object* v_snd_3438_; lean_object* v___y_3444_; lean_object* v_mctx_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v_type_3410_ = lean_ctor_get(v_val_3370_, 3);
v_value_3411_ = lean_ctor_get(v_val_3370_, 4);
v___x_3412_ = lean_st_ref_get(v___y_3352_);
v_mctx_3448_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_mctx_3448_);
lean_dec(v___x_3412_);
v___x_3449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v_mctx_3448_);
v___x_3451_ = l_Lean_Expr_hasFVar(v_type_3410_);
if (v___x_3451_ == 0)
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Expr_hasMVar(v_type_3410_);
if (v___x_3452_ == 0)
{
v_fst_3437_ = v___x_3452_;
v_snd_3438_ = v___x_3450_;
goto v___jp_3436_;
}
else
{
lean_object* v___x_3453_; 
lean_inc_ref(v_type_3410_);
lean_inc_ref(v___f_3376_);
v___x_3453_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3410_, v___x_3450_);
v___y_3444_ = v___x_3453_;
goto v___jp_3443_;
}
}
else
{
lean_object* v___x_3454_; 
lean_inc_ref(v_type_3410_);
lean_inc_ref(v___f_3376_);
v___x_3454_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3410_, v___x_3450_);
v___y_3444_ = v___x_3454_;
goto v___jp_3443_;
}
v___jp_3413_:
{
lean_object* v_mctx_3416_; lean_object* v___x_3417_; lean_object* v_cache_3418_; lean_object* v_zetaDeltaFVarIds_3419_; lean_object* v_postponed_3420_; lean_object* v_diag_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3429_; 
v_mctx_3416_ = lean_ctor_get(v_snd_3415_, 1);
lean_inc_ref(v_mctx_3416_);
lean_dec_ref(v_snd_3415_);
v___x_3417_ = lean_st_ref_take(v___y_3352_);
v_cache_3418_ = lean_ctor_get(v___x_3417_, 1);
v_zetaDeltaFVarIds_3419_ = lean_ctor_get(v___x_3417_, 2);
v_postponed_3420_ = lean_ctor_get(v___x_3417_, 3);
v_diag_3421_ = lean_ctor_get(v___x_3417_, 4);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v___x_3417_, 0);
lean_dec(v_unused_3430_);
v___x_3423_ = v___x_3417_;
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_diag_3421_);
lean_inc(v_postponed_3420_);
lean_inc(v_zetaDeltaFVarIds_3419_);
lean_inc(v_cache_3418_);
lean_dec(v___x_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v_mctx_3416_);
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_mctx_3416_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_cache_3418_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_zetaDeltaFVarIds_3419_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_postponed_3420_);
lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_diag_3421_);
v___x_3426_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_st_ref_put(v___y_3352_, v___x_3426_);
v_a_3372_ = v_fst_3414_;
goto v___jp_3371_;
}
}
}
v___jp_3431_:
{
lean_object* v_fst_3433_; lean_object* v_snd_3434_; uint8_t v___x_3435_; 
v_fst_3433_ = lean_ctor_get(v___y_3432_, 0);
lean_inc(v_fst_3433_);
v_snd_3434_ = lean_ctor_get(v___y_3432_, 1);
lean_inc(v_snd_3434_);
lean_dec_ref(v___y_3432_);
v___x_3435_ = lean_unbox(v_fst_3433_);
lean_dec(v_fst_3433_);
v_fst_3414_ = v___x_3435_;
v_snd_3415_ = v_snd_3434_;
goto v___jp_3413_;
}
v___jp_3436_:
{
if (v_fst_3437_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = l_Lean_Expr_hasFVar(v_value_3411_);
if (v___x_3439_ == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Lean_Expr_hasMVar(v_value_3411_);
if (v___x_3440_ == 0)
{
lean_dec_ref(v___f_3376_);
v_fst_3414_ = v___x_3440_;
v_snd_3415_ = v_snd_3438_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3441_; 
lean_inc_ref(v_value_3411_);
v___x_3441_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_value_3411_, v_snd_3438_);
v___y_3432_ = v___x_3441_;
goto v___jp_3431_;
}
}
else
{
lean_object* v___x_3442_; 
lean_inc_ref(v_value_3411_);
v___x_3442_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_value_3411_, v_snd_3438_);
v___y_3432_ = v___x_3442_;
goto v___jp_3431_;
}
}
else
{
lean_dec_ref(v___f_3376_);
v_fst_3414_ = v_fst_3437_;
v_snd_3415_ = v_snd_3438_;
goto v___jp_3413_;
}
}
v___jp_3443_:
{
lean_object* v_fst_3445_; lean_object* v_snd_3446_; uint8_t v___x_3447_; 
v_fst_3445_ = lean_ctor_get(v___y_3444_, 0);
lean_inc(v_fst_3445_);
v_snd_3446_ = lean_ctor_get(v___y_3444_, 1);
lean_inc(v_snd_3446_);
lean_dec_ref(v___y_3444_);
v___x_3447_ = lean_unbox(v_fst_3445_);
lean_dec(v_fst_3445_);
v_fst_3437_ = v___x_3447_;
v_snd_3438_ = v_snd_3446_;
goto v___jp_3436_;
}
}
else
{
lean_object* v_type_3455_; lean_object* v___x_3456_; uint8_t v_fst_3458_; lean_object* v_mctx_3459_; lean_object* v___y_3475_; lean_object* v_mctx_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v_type_3455_ = lean_ctor_get(v_val_3370_, 3);
v___x_3456_ = lean_st_ref_get(v___y_3352_);
v_mctx_3480_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_ref_n(v_mctx_3480_, 2);
lean_dec(v___x_3456_);
v___x_3481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v_mctx_3480_);
v___x_3483_ = l_Lean_Expr_hasFVar(v_type_3455_);
if (v___x_3483_ == 0)
{
uint8_t v___x_3484_; 
v___x_3484_ = l_Lean_Expr_hasMVar(v_type_3455_);
if (v___x_3484_ == 0)
{
lean_dec_ref_known(v___x_3482_, 2);
lean_dec_ref(v___f_3376_);
v_fst_3458_ = v___x_3484_;
v_mctx_3459_ = v_mctx_3480_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3485_; 
lean_dec_ref(v_mctx_3480_);
lean_inc_ref(v_type_3455_);
v___x_3485_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3455_, v___x_3482_);
v___y_3475_ = v___x_3485_;
goto v___jp_3474_;
}
}
else
{
lean_object* v___x_3486_; 
lean_dec_ref(v_mctx_3480_);
lean_inc_ref(v_type_3455_);
v___x_3486_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3376_, v___f_3375_, v_type_3455_, v___x_3482_);
v___y_3475_ = v___x_3486_;
goto v___jp_3474_;
}
v___jp_3457_:
{
lean_object* v___x_3460_; lean_object* v_cache_3461_; lean_object* v_zetaDeltaFVarIds_3462_; lean_object* v_postponed_3463_; lean_object* v_diag_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3472_; 
v___x_3460_ = lean_st_ref_take(v___y_3352_);
v_cache_3461_ = lean_ctor_get(v___x_3460_, 1);
v_zetaDeltaFVarIds_3462_ = lean_ctor_get(v___x_3460_, 2);
v_postponed_3463_ = lean_ctor_get(v___x_3460_, 3);
v_diag_3464_ = lean_ctor_get(v___x_3460_, 4);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3473_);
v___x_3466_ = v___x_3460_;
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_diag_3464_);
lean_inc(v_postponed_3463_);
lean_inc(v_zetaDeltaFVarIds_3462_);
lean_inc(v_cache_3461_);
lean_dec(v___x_3460_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v_mctx_3459_);
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_mctx_3459_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_cache_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_zetaDeltaFVarIds_3462_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_postponed_3463_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_diag_3464_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; 
v___x_3470_ = lean_st_ref_put(v___y_3352_, v___x_3469_);
v_a_3372_ = v_fst_3458_;
goto v___jp_3371_;
}
}
}
v___jp_3474_:
{
lean_object* v_snd_3476_; lean_object* v_fst_3477_; lean_object* v_mctx_3478_; uint8_t v___x_3479_; 
v_snd_3476_ = lean_ctor_get(v___y_3475_, 1);
lean_inc(v_snd_3476_);
v_fst_3477_ = lean_ctor_get(v___y_3475_, 0);
lean_inc(v_fst_3477_);
lean_dec_ref(v___y_3475_);
v_mctx_3478_ = lean_ctor_get(v_snd_3476_, 1);
lean_inc_ref(v_mctx_3478_);
lean_dec(v_snd_3476_);
v___x_3479_ = lean_unbox(v_fst_3477_);
lean_dec(v_fst_3477_);
v_fst_3458_ = v___x_3479_;
v_mctx_3459_ = v_mctx_3478_;
goto v___jp_3457_;
}
}
}
v___jp_3371_:
{
if (v_a_3372_ == 0)
{
v_a_3362_ = v_snd_3356_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = l_Lean_LocalDecl_fvarId(v_val_3370_);
v___x_3374_ = lean_array_push(v_snd_3356_, v___x_3373_);
v_a_3362_ = v___x_3374_;
goto v___jp_3361_;
}
}
}
v___jp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_a_3362_);
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3364_ = v___x_3358_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_a_3362_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3350_, v___x_3365_);
v_i_3350_ = v___x_3366_;
v_b_3351_ = v___x_3364_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3489_, lean_object* v_sz_3490_, lean_object* v_i_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3490_);
lean_dec(v_sz_3490_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3491_);
lean_dec(v_i_3491_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3489_, v_sz_boxed_3495_, v_i_boxed_3496_, v_b_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v_as_3489_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3498_, size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_usize_dec_lt(v_i_3500_, v_sz_3499_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_b_3501_);
return v___x_3508_;
}
else
{
lean_object* v_snd_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3640_; 
v_snd_3509_ = lean_ctor_get(v_b_3501_, 1);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_b_3501_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v_b_3501_, 0);
lean_dec(v_unused_3641_);
v___x_3511_ = v_b_3501_;
v_isShared_3512_ = v_isSharedCheck_3640_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_snd_3509_);
lean_dec(v_b_3501_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3640_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v_a_3515_; lean_object* v_a_3522_; 
v___x_3513_ = lean_box(0);
v_a_3522_ = lean_array_uget_borrowed(v_as_3498_, v_i_3500_);
if (lean_obj_tag(v_a_3522_) == 0)
{
v_a_3515_ = v_snd_3509_;
goto v___jp_3514_;
}
else
{
lean_object* v_val_3523_; uint8_t v_a_3525_; lean_object* v___f_3528_; lean_object* v___f_3529_; 
v_val_3523_ = lean_ctor_get(v_a_3522_, 0);
v___f_3528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3509_);
v___f_3529_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3529_, 0, v_snd_3509_);
if (lean_obj_tag(v_val_3523_) == 0)
{
lean_object* v_type_3530_; lean_object* v___x_3531_; uint8_t v_fst_3533_; lean_object* v_mctx_3534_; lean_object* v___y_3550_; lean_object* v_mctx_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_type_3530_ = lean_ctor_get(v_val_3523_, 3);
v___x_3531_ = lean_st_ref_get(v___y_3503_);
v_mctx_3555_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref_n(v_mctx_3555_, 2);
lean_dec(v___x_3531_);
v___x_3556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v_mctx_3555_);
v___x_3558_ = l_Lean_Expr_hasFVar(v_type_3530_);
if (v___x_3558_ == 0)
{
uint8_t v___x_3559_; 
v___x_3559_ = l_Lean_Expr_hasMVar(v_type_3530_);
if (v___x_3559_ == 0)
{
lean_dec_ref_known(v___x_3557_, 2);
lean_dec_ref(v___f_3529_);
v_fst_3533_ = v___x_3559_;
v_mctx_3534_ = v_mctx_3555_;
goto v___jp_3532_;
}
else
{
lean_object* v___x_3560_; 
lean_dec_ref(v_mctx_3555_);
lean_inc_ref(v_type_3530_);
v___x_3560_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3530_, v___x_3557_);
v___y_3550_ = v___x_3560_;
goto v___jp_3549_;
}
}
else
{
lean_object* v___x_3561_; 
lean_dec_ref(v_mctx_3555_);
lean_inc_ref(v_type_3530_);
v___x_3561_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3530_, v___x_3557_);
v___y_3550_ = v___x_3561_;
goto v___jp_3549_;
}
v___jp_3532_:
{
lean_object* v___x_3535_; lean_object* v_cache_3536_; lean_object* v_zetaDeltaFVarIds_3537_; lean_object* v_postponed_3538_; lean_object* v_diag_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3547_; 
v___x_3535_ = lean_st_ref_take(v___y_3503_);
v_cache_3536_ = lean_ctor_get(v___x_3535_, 1);
v_zetaDeltaFVarIds_3537_ = lean_ctor_get(v___x_3535_, 2);
v_postponed_3538_ = lean_ctor_get(v___x_3535_, 3);
v_diag_3539_ = lean_ctor_get(v___x_3535_, 4);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3548_);
v___x_3541_ = v___x_3535_;
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_diag_3539_);
lean_inc(v_postponed_3538_);
lean_inc(v_zetaDeltaFVarIds_3537_);
lean_inc(v_cache_3536_);
lean_dec(v___x_3535_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v_mctx_3534_);
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_mctx_3534_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_cache_3536_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_zetaDeltaFVarIds_3537_);
lean_ctor_set(v_reuseFailAlloc_3546_, 3, v_postponed_3538_);
lean_ctor_set(v_reuseFailAlloc_3546_, 4, v_diag_3539_);
v___x_3544_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_st_ref_put(v___y_3503_, v___x_3544_);
v_a_3525_ = v_fst_3533_;
goto v___jp_3524_;
}
}
}
v___jp_3549_:
{
lean_object* v_snd_3551_; lean_object* v_fst_3552_; lean_object* v_mctx_3553_; uint8_t v___x_3554_; 
v_snd_3551_ = lean_ctor_get(v___y_3550_, 1);
lean_inc(v_snd_3551_);
v_fst_3552_ = lean_ctor_get(v___y_3550_, 0);
lean_inc(v_fst_3552_);
lean_dec_ref(v___y_3550_);
v_mctx_3553_ = lean_ctor_get(v_snd_3551_, 1);
lean_inc_ref(v_mctx_3553_);
lean_dec(v_snd_3551_);
v___x_3554_ = lean_unbox(v_fst_3552_);
lean_dec(v_fst_3552_);
v_fst_3533_ = v___x_3554_;
v_mctx_3534_ = v_mctx_3553_;
goto v___jp_3532_;
}
}
else
{
uint8_t v_nondep_3562_; 
v_nondep_3562_ = lean_ctor_get_uint8(v_val_3523_, sizeof(void*)*5);
if (v_nondep_3562_ == 0)
{
lean_object* v_type_3563_; lean_object* v_value_3564_; lean_object* v___x_3565_; uint8_t v_fst_3567_; lean_object* v_snd_3568_; lean_object* v___y_3585_; uint8_t v_fst_3590_; lean_object* v_snd_3591_; lean_object* v___y_3597_; lean_object* v_mctx_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_type_3563_ = lean_ctor_get(v_val_3523_, 3);
v_value_3564_ = lean_ctor_get(v_val_3523_, 4);
v___x_3565_ = lean_st_ref_get(v___y_3503_);
v_mctx_3601_ = lean_ctor_get(v___x_3565_, 0);
lean_inc_ref(v_mctx_3601_);
lean_dec(v___x_3565_);
v___x_3602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_mctx_3601_);
v___x_3604_ = l_Lean_Expr_hasFVar(v_type_3563_);
if (v___x_3604_ == 0)
{
uint8_t v___x_3605_; 
v___x_3605_ = l_Lean_Expr_hasMVar(v_type_3563_);
if (v___x_3605_ == 0)
{
v_fst_3590_ = v___x_3605_;
v_snd_3591_ = v___x_3603_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3606_; 
lean_inc_ref(v_type_3563_);
lean_inc_ref(v___f_3529_);
v___x_3606_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3563_, v___x_3603_);
v___y_3597_ = v___x_3606_;
goto v___jp_3596_;
}
}
else
{
lean_object* v___x_3607_; 
lean_inc_ref(v_type_3563_);
lean_inc_ref(v___f_3529_);
v___x_3607_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3563_, v___x_3603_);
v___y_3597_ = v___x_3607_;
goto v___jp_3596_;
}
v___jp_3566_:
{
lean_object* v_mctx_3569_; lean_object* v___x_3570_; lean_object* v_cache_3571_; lean_object* v_zetaDeltaFVarIds_3572_; lean_object* v_postponed_3573_; lean_object* v_diag_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3582_; 
v_mctx_3569_ = lean_ctor_get(v_snd_3568_, 1);
lean_inc_ref(v_mctx_3569_);
lean_dec_ref(v_snd_3568_);
v___x_3570_ = lean_st_ref_take(v___y_3503_);
v_cache_3571_ = lean_ctor_get(v___x_3570_, 1);
v_zetaDeltaFVarIds_3572_ = lean_ctor_get(v___x_3570_, 2);
v_postponed_3573_ = lean_ctor_get(v___x_3570_, 3);
v_diag_3574_ = lean_ctor_get(v___x_3570_, 4);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; 
v_unused_3583_ = lean_ctor_get(v___x_3570_, 0);
lean_dec(v_unused_3583_);
v___x_3576_ = v___x_3570_;
v_isShared_3577_ = v_isSharedCheck_3582_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_diag_3574_);
lean_inc(v_postponed_3573_);
lean_inc(v_zetaDeltaFVarIds_3572_);
lean_inc(v_cache_3571_);
lean_dec(v___x_3570_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3582_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v_mctx_3569_);
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_mctx_3569_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_cache_3571_);
lean_ctor_set(v_reuseFailAlloc_3581_, 2, v_zetaDeltaFVarIds_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 3, v_postponed_3573_);
lean_ctor_set(v_reuseFailAlloc_3581_, 4, v_diag_3574_);
v___x_3579_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_st_ref_put(v___y_3503_, v___x_3579_);
v_a_3525_ = v_fst_3567_;
goto v___jp_3524_;
}
}
}
v___jp_3584_:
{
lean_object* v_fst_3586_; lean_object* v_snd_3587_; uint8_t v___x_3588_; 
v_fst_3586_ = lean_ctor_get(v___y_3585_, 0);
lean_inc(v_fst_3586_);
v_snd_3587_ = lean_ctor_get(v___y_3585_, 1);
lean_inc(v_snd_3587_);
lean_dec_ref(v___y_3585_);
v___x_3588_ = lean_unbox(v_fst_3586_);
lean_dec(v_fst_3586_);
v_fst_3567_ = v___x_3588_;
v_snd_3568_ = v_snd_3587_;
goto v___jp_3566_;
}
v___jp_3589_:
{
if (v_fst_3590_ == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Lean_Expr_hasFVar(v_value_3564_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = l_Lean_Expr_hasMVar(v_value_3564_);
if (v___x_3593_ == 0)
{
lean_dec_ref(v___f_3529_);
v_fst_3567_ = v___x_3593_;
v_snd_3568_ = v_snd_3591_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3594_; 
lean_inc_ref(v_value_3564_);
v___x_3594_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_value_3564_, v_snd_3591_);
v___y_3585_ = v___x_3594_;
goto v___jp_3584_;
}
}
else
{
lean_object* v___x_3595_; 
lean_inc_ref(v_value_3564_);
v___x_3595_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_value_3564_, v_snd_3591_);
v___y_3585_ = v___x_3595_;
goto v___jp_3584_;
}
}
else
{
lean_dec_ref(v___f_3529_);
v_fst_3567_ = v_fst_3590_;
v_snd_3568_ = v_snd_3591_;
goto v___jp_3566_;
}
}
v___jp_3596_:
{
lean_object* v_fst_3598_; lean_object* v_snd_3599_; uint8_t v___x_3600_; 
v_fst_3598_ = lean_ctor_get(v___y_3597_, 0);
lean_inc(v_fst_3598_);
v_snd_3599_ = lean_ctor_get(v___y_3597_, 1);
lean_inc(v_snd_3599_);
lean_dec_ref(v___y_3597_);
v___x_3600_ = lean_unbox(v_fst_3598_);
lean_dec(v_fst_3598_);
v_fst_3590_ = v___x_3600_;
v_snd_3591_ = v_snd_3599_;
goto v___jp_3589_;
}
}
else
{
lean_object* v_type_3608_; lean_object* v___x_3609_; uint8_t v_fst_3611_; lean_object* v_mctx_3612_; lean_object* v___y_3628_; lean_object* v_mctx_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v_type_3608_ = lean_ctor_get(v_val_3523_, 3);
v___x_3609_ = lean_st_ref_get(v___y_3503_);
v_mctx_3633_ = lean_ctor_get(v___x_3609_, 0);
lean_inc_ref_n(v_mctx_3633_, 2);
lean_dec(v___x_3609_);
v___x_3634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v_mctx_3633_);
v___x_3636_ = l_Lean_Expr_hasFVar(v_type_3608_);
if (v___x_3636_ == 0)
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_Expr_hasMVar(v_type_3608_);
if (v___x_3637_ == 0)
{
lean_dec_ref_known(v___x_3635_, 2);
lean_dec_ref(v___f_3529_);
v_fst_3611_ = v___x_3637_;
v_mctx_3612_ = v_mctx_3633_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3638_; 
lean_dec_ref(v_mctx_3633_);
lean_inc_ref(v_type_3608_);
v___x_3638_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3608_, v___x_3635_);
v___y_3628_ = v___x_3638_;
goto v___jp_3627_;
}
}
else
{
lean_object* v___x_3639_; 
lean_dec_ref(v_mctx_3633_);
lean_inc_ref(v_type_3608_);
v___x_3639_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3529_, v___f_3528_, v_type_3608_, v___x_3635_);
v___y_3628_ = v___x_3639_;
goto v___jp_3627_;
}
v___jp_3610_:
{
lean_object* v___x_3613_; lean_object* v_cache_3614_; lean_object* v_zetaDeltaFVarIds_3615_; lean_object* v_postponed_3616_; lean_object* v_diag_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3625_; 
v___x_3613_ = lean_st_ref_take(v___y_3503_);
v_cache_3614_ = lean_ctor_get(v___x_3613_, 1);
v_zetaDeltaFVarIds_3615_ = lean_ctor_get(v___x_3613_, 2);
v_postponed_3616_ = lean_ctor_get(v___x_3613_, 3);
v_diag_3617_ = lean_ctor_get(v___x_3613_, 4);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; 
v_unused_3626_ = lean_ctor_get(v___x_3613_, 0);
lean_dec(v_unused_3626_);
v___x_3619_ = v___x_3613_;
v_isShared_3620_ = v_isSharedCheck_3625_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_diag_3617_);
lean_inc(v_postponed_3616_);
lean_inc(v_zetaDeltaFVarIds_3615_);
lean_inc(v_cache_3614_);
lean_dec(v___x_3613_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3625_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v_mctx_3612_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_mctx_3612_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_cache_3614_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_zetaDeltaFVarIds_3615_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_postponed_3616_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_diag_3617_);
v___x_3622_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; 
v___x_3623_ = lean_st_ref_put(v___y_3503_, v___x_3622_);
v_a_3525_ = v_fst_3611_;
goto v___jp_3524_;
}
}
}
v___jp_3627_:
{
lean_object* v_snd_3629_; lean_object* v_fst_3630_; lean_object* v_mctx_3631_; uint8_t v___x_3632_; 
v_snd_3629_ = lean_ctor_get(v___y_3628_, 1);
lean_inc(v_snd_3629_);
v_fst_3630_ = lean_ctor_get(v___y_3628_, 0);
lean_inc(v_fst_3630_);
lean_dec_ref(v___y_3628_);
v_mctx_3631_ = lean_ctor_get(v_snd_3629_, 1);
lean_inc_ref(v_mctx_3631_);
lean_dec(v_snd_3629_);
v___x_3632_ = lean_unbox(v_fst_3630_);
lean_dec(v_fst_3630_);
v_fst_3611_ = v___x_3632_;
v_mctx_3612_ = v_mctx_3631_;
goto v___jp_3610_;
}
}
}
v___jp_3524_:
{
if (v_a_3525_ == 0)
{
v_a_3515_ = v_snd_3509_;
goto v___jp_3514_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = l_Lean_LocalDecl_fvarId(v_val_3523_);
v___x_3527_ = lean_array_push(v_snd_3509_, v___x_3526_);
v_a_3515_ = v___x_3527_;
goto v___jp_3514_;
}
}
}
v___jp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_a_3515_);
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3517_ = v___x_3511_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_a_3515_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
size_t v___x_3518_; size_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((size_t)1ULL);
v___x_3519_ = lean_usize_add(v_i_3500_, v___x_3518_);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3498_, v_sz_3499_, v___x_3519_, v___x_3517_, v___y_3503_);
return v___x_3520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3642_, lean_object* v_sz_3643_, lean_object* v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
size_t v_sz_boxed_3651_; size_t v_i_boxed_3652_; lean_object* v_res_3653_; 
v_sz_boxed_3651_ = lean_unbox_usize(v_sz_3643_);
lean_dec(v_sz_3643_);
v_i_boxed_3652_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_res_3653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3642_, v_sz_boxed_3651_, v_i_boxed_3652_, v_b_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_as_3642_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3654_, lean_object* v_n_3655_, lean_object* v_b_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
if (lean_obj_tag(v_n_3655_) == 0)
{
lean_object* v_cs_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; size_t v_sz_3665_; size_t v___x_3666_; lean_object* v___x_3667_; 
v_cs_3662_ = lean_ctor_get(v_n_3655_, 0);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v_b_3656_);
v_sz_3665_ = lean_array_size(v_cs_3662_);
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3654_, v_cs_3662_, v_sz_3665_, v___x_3666_, v___x_3664_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3682_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3682_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3682_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_fst_3672_; 
v_fst_3672_ = lean_ctor_get(v_a_3668_, 0);
if (lean_obj_tag(v_fst_3672_) == 0)
{
lean_object* v_snd_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v_snd_3673_ = lean_ctor_get(v_a_3668_, 1);
lean_inc(v_snd_3673_);
lean_dec(v_a_3668_);
v___x_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3674_, 0, v_snd_3673_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3674_);
v___x_3676_ = v___x_3670_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
else
{
lean_object* v_val_3678_; lean_object* v___x_3680_; 
lean_inc_ref(v_fst_3672_);
lean_dec(v_a_3668_);
v_val_3678_ = lean_ctor_get(v_fst_3672_, 0);
lean_inc(v_val_3678_);
lean_dec_ref_known(v_fst_3672_, 1);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_val_3678_);
v___x_3680_ = v___x_3670_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_val_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
v_a_3683_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3667_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3667_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_vs_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; size_t v_sz_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v_vs_3691_ = lean_ctor_get(v_n_3655_, 0);
v___x_3692_ = lean_box(0);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v_b_3656_);
v_sz_3694_ = lean_array_size(v_vs_3691_);
v___x_3695_ = ((size_t)0ULL);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3691_, v_sz_3694_, v___x_3695_, v___x_3693_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3711_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3711_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3711_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v_fst_3701_; 
v_fst_3701_ = lean_ctor_get(v_a_3697_, 0);
if (lean_obj_tag(v_fst_3701_) == 0)
{
lean_object* v_snd_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v_snd_3702_ = lean_ctor_get(v_a_3697_, 1);
lean_inc(v_snd_3702_);
lean_dec(v_a_3697_);
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_snd_3702_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3703_);
v___x_3705_ = v___x_3699_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3709_; 
lean_inc_ref(v_fst_3701_);
lean_dec(v_a_3697_);
v_val_3707_ = lean_ctor_get(v_fst_3701_, 0);
lean_inc(v_val_3707_);
lean_dec_ref_known(v_fst_3701_, 1);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v_val_3707_);
v___x_3709_ = v___x_3699_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_val_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_a_3712_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3696_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3696_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3720_, lean_object* v_as_3721_, size_t v_sz_3722_, size_t v_i_3723_, lean_object* v_b_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_usize_dec_lt(v_i_3723_, v_sz_3722_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_b_3724_);
return v___x_3731_;
}
else
{
lean_object* v_snd_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3766_; 
v_snd_3732_ = lean_ctor_get(v_b_3724_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_b_3724_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; 
v_unused_3767_ = lean_ctor_get(v_b_3724_, 0);
lean_dec(v_unused_3767_);
v___x_3734_ = v_b_3724_;
v_isShared_3735_ = v_isSharedCheck_3766_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_snd_3732_);
lean_dec(v_b_3724_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3766_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v_a_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_box(0);
v_a_3737_ = lean_array_uget_borrowed(v_as_3721_, v_i_3723_);
lean_inc(v_snd_3732_);
v___x_3738_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3720_, v_a_3737_, v_snd_3732_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3757_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3757_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3757_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
if (lean_obj_tag(v_a_3739_) == 0)
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_a_3739_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3743_);
v___x_3745_ = v___x_3734_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_snd_3732_);
v___x_3745_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3747_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3745_);
v___x_3747_ = v___x_3741_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; 
lean_del_object(v___x_3741_);
lean_dec(v_snd_3732_);
v_a_3750_ = lean_ctor_get(v_a_3739_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v_a_3739_, 1);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v_a_3750_);
lean_ctor_set(v___x_3734_, 0, v___x_3736_);
v___x_3752_ = v___x_3734_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_a_3750_);
v___x_3752_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
size_t v___x_3753_; size_t v___x_3754_; 
v___x_3753_ = ((size_t)1ULL);
v___x_3754_ = lean_usize_add(v_i_3723_, v___x_3753_);
v_i_3723_ = v___x_3754_;
v_b_3724_ = v___x_3752_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_del_object(v___x_3734_);
lean_dec(v_snd_3732_);
v_a_3758_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3738_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3738_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3768_, lean_object* v_as_3769_, lean_object* v_sz_3770_, lean_object* v_i_3771_, lean_object* v_b_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
size_t v_sz_boxed_3778_; size_t v_i_boxed_3779_; lean_object* v_res_3780_; 
v_sz_boxed_3778_ = lean_unbox_usize(v_sz_3770_);
lean_dec(v_sz_3770_);
v_i_boxed_3779_ = lean_unbox_usize(v_i_3771_);
lean_dec(v_i_3771_);
v_res_3780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3768_, v_as_3769_, v_sz_boxed_3778_, v_i_boxed_3779_, v_b_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec_ref(v_as_3769_);
lean_dec_ref(v_init_3768_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3781_, lean_object* v_n_3782_, lean_object* v_b_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3781_, v_n_3782_, v_b_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v_n_3782_);
lean_dec_ref(v_init_3781_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3790_, size_t v_sz_3791_, size_t v_i_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_usize_dec_lt(v_i_3792_, v_sz_3791_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_b_3793_);
return v___x_3797_;
}
else
{
lean_object* v_snd_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3929_; 
v_snd_3798_ = lean_ctor_get(v_b_3793_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_b_3793_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_b_3793_, 0);
lean_dec(v_unused_3930_);
v___x_3800_ = v_b_3793_;
v_isShared_3801_ = v_isSharedCheck_3929_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_snd_3798_);
lean_dec(v_b_3793_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3929_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v_a_3804_; lean_object* v_a_3811_; 
v___x_3802_ = lean_box(0);
v_a_3811_ = lean_array_uget_borrowed(v_as_3790_, v_i_3792_);
if (lean_obj_tag(v_a_3811_) == 0)
{
v_a_3804_ = v_snd_3798_;
goto v___jp_3803_;
}
else
{
lean_object* v_val_3812_; uint8_t v_a_3814_; lean_object* v___f_3817_; lean_object* v___f_3818_; 
v_val_3812_ = lean_ctor_get(v_a_3811_, 0);
v___f_3817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3798_);
v___f_3818_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3818_, 0, v_snd_3798_);
if (lean_obj_tag(v_val_3812_) == 0)
{
lean_object* v_type_3819_; lean_object* v___x_3820_; uint8_t v_fst_3822_; lean_object* v_mctx_3823_; lean_object* v___y_3839_; lean_object* v_mctx_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_type_3819_ = lean_ctor_get(v_val_3812_, 3);
v___x_3820_ = lean_st_ref_get(v___y_3794_);
v_mctx_3844_ = lean_ctor_get(v___x_3820_, 0);
lean_inc_ref_n(v_mctx_3844_, 2);
lean_dec(v___x_3820_);
v___x_3845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
lean_ctor_set(v___x_3846_, 1, v_mctx_3844_);
v___x_3847_ = l_Lean_Expr_hasFVar(v_type_3819_);
if (v___x_3847_ == 0)
{
uint8_t v___x_3848_; 
v___x_3848_ = l_Lean_Expr_hasMVar(v_type_3819_);
if (v___x_3848_ == 0)
{
lean_dec_ref_known(v___x_3846_, 2);
lean_dec_ref(v___f_3818_);
v_fst_3822_ = v___x_3848_;
v_mctx_3823_ = v_mctx_3844_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3849_; 
lean_dec_ref(v_mctx_3844_);
lean_inc_ref(v_type_3819_);
v___x_3849_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3819_, v___x_3846_);
v___y_3839_ = v___x_3849_;
goto v___jp_3838_;
}
}
else
{
lean_object* v___x_3850_; 
lean_dec_ref(v_mctx_3844_);
lean_inc_ref(v_type_3819_);
v___x_3850_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3819_, v___x_3846_);
v___y_3839_ = v___x_3850_;
goto v___jp_3838_;
}
v___jp_3821_:
{
lean_object* v___x_3824_; lean_object* v_cache_3825_; lean_object* v_zetaDeltaFVarIds_3826_; lean_object* v_postponed_3827_; lean_object* v_diag_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
v___x_3824_ = lean_st_ref_take(v___y_3794_);
v_cache_3825_ = lean_ctor_get(v___x_3824_, 1);
v_zetaDeltaFVarIds_3826_ = lean_ctor_get(v___x_3824_, 2);
v_postponed_3827_ = lean_ctor_get(v___x_3824_, 3);
v_diag_3828_ = lean_ctor_get(v___x_3824_, 4);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; 
v_unused_3837_ = lean_ctor_get(v___x_3824_, 0);
lean_dec(v_unused_3837_);
v___x_3830_ = v___x_3824_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_diag_3828_);
lean_inc(v_postponed_3827_);
lean_inc(v_zetaDeltaFVarIds_3826_);
lean_inc(v_cache_3825_);
lean_dec(v___x_3824_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v_mctx_3823_);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_mctx_3823_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_cache_3825_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_zetaDeltaFVarIds_3826_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_postponed_3827_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_diag_3828_);
v___x_3833_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_st_ref_put(v___y_3794_, v___x_3833_);
v_a_3814_ = v_fst_3822_;
goto v___jp_3813_;
}
}
}
v___jp_3838_:
{
lean_object* v_snd_3840_; lean_object* v_fst_3841_; lean_object* v_mctx_3842_; uint8_t v___x_3843_; 
v_snd_3840_ = lean_ctor_get(v___y_3839_, 1);
lean_inc(v_snd_3840_);
v_fst_3841_ = lean_ctor_get(v___y_3839_, 0);
lean_inc(v_fst_3841_);
lean_dec_ref(v___y_3839_);
v_mctx_3842_ = lean_ctor_get(v_snd_3840_, 1);
lean_inc_ref(v_mctx_3842_);
lean_dec(v_snd_3840_);
v___x_3843_ = lean_unbox(v_fst_3841_);
lean_dec(v_fst_3841_);
v_fst_3822_ = v___x_3843_;
v_mctx_3823_ = v_mctx_3842_;
goto v___jp_3821_;
}
}
else
{
uint8_t v_nondep_3851_; 
v_nondep_3851_ = lean_ctor_get_uint8(v_val_3812_, sizeof(void*)*5);
if (v_nondep_3851_ == 0)
{
lean_object* v_type_3852_; lean_object* v_value_3853_; lean_object* v___x_3854_; uint8_t v_fst_3856_; lean_object* v_snd_3857_; lean_object* v___y_3874_; uint8_t v_fst_3879_; lean_object* v_snd_3880_; lean_object* v___y_3886_; lean_object* v_mctx_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_type_3852_ = lean_ctor_get(v_val_3812_, 3);
v_value_3853_ = lean_ctor_get(v_val_3812_, 4);
v___x_3854_ = lean_st_ref_get(v___y_3794_);
v_mctx_3890_ = lean_ctor_get(v___x_3854_, 0);
lean_inc_ref(v_mctx_3890_);
lean_dec(v___x_3854_);
v___x_3891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v_mctx_3890_);
v___x_3893_ = l_Lean_Expr_hasFVar(v_type_3852_);
if (v___x_3893_ == 0)
{
uint8_t v___x_3894_; 
v___x_3894_ = l_Lean_Expr_hasMVar(v_type_3852_);
if (v___x_3894_ == 0)
{
v_fst_3879_ = v___x_3894_;
v_snd_3880_ = v___x_3892_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3895_; 
lean_inc_ref(v_type_3852_);
lean_inc_ref(v___f_3818_);
v___x_3895_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3852_, v___x_3892_);
v___y_3886_ = v___x_3895_;
goto v___jp_3885_;
}
}
else
{
lean_object* v___x_3896_; 
lean_inc_ref(v_type_3852_);
lean_inc_ref(v___f_3818_);
v___x_3896_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3852_, v___x_3892_);
v___y_3886_ = v___x_3896_;
goto v___jp_3885_;
}
v___jp_3855_:
{
lean_object* v_mctx_3858_; lean_object* v___x_3859_; lean_object* v_cache_3860_; lean_object* v_zetaDeltaFVarIds_3861_; lean_object* v_postponed_3862_; lean_object* v_diag_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3871_; 
v_mctx_3858_ = lean_ctor_get(v_snd_3857_, 1);
lean_inc_ref(v_mctx_3858_);
lean_dec_ref(v_snd_3857_);
v___x_3859_ = lean_st_ref_take(v___y_3794_);
v_cache_3860_ = lean_ctor_get(v___x_3859_, 1);
v_zetaDeltaFVarIds_3861_ = lean_ctor_get(v___x_3859_, 2);
v_postponed_3862_ = lean_ctor_get(v___x_3859_, 3);
v_diag_3863_ = lean_ctor_get(v___x_3859_, 4);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v___x_3859_, 0);
lean_dec(v_unused_3872_);
v___x_3865_ = v___x_3859_;
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_diag_3863_);
lean_inc(v_postponed_3862_);
lean_inc(v_zetaDeltaFVarIds_3861_);
lean_inc(v_cache_3860_);
lean_dec(v___x_3859_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 0, v_mctx_3858_);
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_mctx_3858_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_cache_3860_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_zetaDeltaFVarIds_3861_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_postponed_3862_);
lean_ctor_set(v_reuseFailAlloc_3870_, 4, v_diag_3863_);
v___x_3868_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_st_ref_put(v___y_3794_, v___x_3868_);
v_a_3814_ = v_fst_3856_;
goto v___jp_3813_;
}
}
}
v___jp_3873_:
{
lean_object* v_fst_3875_; lean_object* v_snd_3876_; uint8_t v___x_3877_; 
v_fst_3875_ = lean_ctor_get(v___y_3874_, 0);
lean_inc(v_fst_3875_);
v_snd_3876_ = lean_ctor_get(v___y_3874_, 1);
lean_inc(v_snd_3876_);
lean_dec_ref(v___y_3874_);
v___x_3877_ = lean_unbox(v_fst_3875_);
lean_dec(v_fst_3875_);
v_fst_3856_ = v___x_3877_;
v_snd_3857_ = v_snd_3876_;
goto v___jp_3855_;
}
v___jp_3878_:
{
if (v_fst_3879_ == 0)
{
uint8_t v___x_3881_; 
v___x_3881_ = l_Lean_Expr_hasFVar(v_value_3853_);
if (v___x_3881_ == 0)
{
uint8_t v___x_3882_; 
v___x_3882_ = l_Lean_Expr_hasMVar(v_value_3853_);
if (v___x_3882_ == 0)
{
lean_dec_ref(v___f_3818_);
v_fst_3856_ = v___x_3882_;
v_snd_3857_ = v_snd_3880_;
goto v___jp_3855_;
}
else
{
lean_object* v___x_3883_; 
lean_inc_ref(v_value_3853_);
v___x_3883_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_value_3853_, v_snd_3880_);
v___y_3874_ = v___x_3883_;
goto v___jp_3873_;
}
}
else
{
lean_object* v___x_3884_; 
lean_inc_ref(v_value_3853_);
v___x_3884_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_value_3853_, v_snd_3880_);
v___y_3874_ = v___x_3884_;
goto v___jp_3873_;
}
}
else
{
lean_dec_ref(v___f_3818_);
v_fst_3856_ = v_fst_3879_;
v_snd_3857_ = v_snd_3880_;
goto v___jp_3855_;
}
}
v___jp_3885_:
{
lean_object* v_fst_3887_; lean_object* v_snd_3888_; uint8_t v___x_3889_; 
v_fst_3887_ = lean_ctor_get(v___y_3886_, 0);
lean_inc(v_fst_3887_);
v_snd_3888_ = lean_ctor_get(v___y_3886_, 1);
lean_inc(v_snd_3888_);
lean_dec_ref(v___y_3886_);
v___x_3889_ = lean_unbox(v_fst_3887_);
lean_dec(v_fst_3887_);
v_fst_3879_ = v___x_3889_;
v_snd_3880_ = v_snd_3888_;
goto v___jp_3878_;
}
}
else
{
lean_object* v_type_3897_; lean_object* v___x_3898_; uint8_t v_fst_3900_; lean_object* v_mctx_3901_; lean_object* v___y_3917_; lean_object* v_mctx_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_type_3897_ = lean_ctor_get(v_val_3812_, 3);
v___x_3898_ = lean_st_ref_get(v___y_3794_);
v_mctx_3922_ = lean_ctor_get(v___x_3898_, 0);
lean_inc_ref_n(v_mctx_3922_, 2);
lean_dec(v___x_3898_);
v___x_3923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_mctx_3922_);
v___x_3925_ = l_Lean_Expr_hasFVar(v_type_3897_);
if (v___x_3925_ == 0)
{
uint8_t v___x_3926_; 
v___x_3926_ = l_Lean_Expr_hasMVar(v_type_3897_);
if (v___x_3926_ == 0)
{
lean_dec_ref_known(v___x_3924_, 2);
lean_dec_ref(v___f_3818_);
v_fst_3900_ = v___x_3926_;
v_mctx_3901_ = v_mctx_3922_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3927_; 
lean_dec_ref(v_mctx_3922_);
lean_inc_ref(v_type_3897_);
v___x_3927_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3897_, v___x_3924_);
v___y_3917_ = v___x_3927_;
goto v___jp_3916_;
}
}
else
{
lean_object* v___x_3928_; 
lean_dec_ref(v_mctx_3922_);
lean_inc_ref(v_type_3897_);
v___x_3928_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3818_, v___f_3817_, v_type_3897_, v___x_3924_);
v___y_3917_ = v___x_3928_;
goto v___jp_3916_;
}
v___jp_3899_:
{
lean_object* v___x_3902_; lean_object* v_cache_3903_; lean_object* v_zetaDeltaFVarIds_3904_; lean_object* v_postponed_3905_; lean_object* v_diag_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3914_; 
v___x_3902_ = lean_st_ref_take(v___y_3794_);
v_cache_3903_ = lean_ctor_get(v___x_3902_, 1);
v_zetaDeltaFVarIds_3904_ = lean_ctor_get(v___x_3902_, 2);
v_postponed_3905_ = lean_ctor_get(v___x_3902_, 3);
v_diag_3906_ = lean_ctor_get(v___x_3902_, 4);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; 
v_unused_3915_ = lean_ctor_get(v___x_3902_, 0);
lean_dec(v_unused_3915_);
v___x_3908_ = v___x_3902_;
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_diag_3906_);
lean_inc(v_postponed_3905_);
lean_inc(v_zetaDeltaFVarIds_3904_);
lean_inc(v_cache_3903_);
lean_dec(v___x_3902_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v_mctx_3901_);
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_mctx_3901_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_cache_3903_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_zetaDeltaFVarIds_3904_);
lean_ctor_set(v_reuseFailAlloc_3913_, 3, v_postponed_3905_);
lean_ctor_set(v_reuseFailAlloc_3913_, 4, v_diag_3906_);
v___x_3911_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_st_ref_put(v___y_3794_, v___x_3911_);
v_a_3814_ = v_fst_3900_;
goto v___jp_3813_;
}
}
}
v___jp_3916_:
{
lean_object* v_snd_3918_; lean_object* v_fst_3919_; lean_object* v_mctx_3920_; uint8_t v___x_3921_; 
v_snd_3918_ = lean_ctor_get(v___y_3917_, 1);
lean_inc(v_snd_3918_);
v_fst_3919_ = lean_ctor_get(v___y_3917_, 0);
lean_inc(v_fst_3919_);
lean_dec_ref(v___y_3917_);
v_mctx_3920_ = lean_ctor_get(v_snd_3918_, 1);
lean_inc_ref(v_mctx_3920_);
lean_dec(v_snd_3918_);
v___x_3921_ = lean_unbox(v_fst_3919_);
lean_dec(v_fst_3919_);
v_fst_3900_ = v___x_3921_;
v_mctx_3901_ = v_mctx_3920_;
goto v___jp_3899_;
}
}
}
v___jp_3813_:
{
if (v_a_3814_ == 0)
{
v_a_3804_ = v_snd_3798_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = l_Lean_LocalDecl_fvarId(v_val_3812_);
v___x_3816_ = lean_array_push(v_snd_3798_, v___x_3815_);
v_a_3804_ = v___x_3816_;
goto v___jp_3803_;
}
}
}
v___jp_3803_:
{
lean_object* v___x_3806_; 
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 1, v_a_3804_);
lean_ctor_set(v___x_3800_, 0, v___x_3802_);
v___x_3806_ = v___x_3800_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_a_3804_);
v___x_3806_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
size_t v___x_3807_; size_t v___x_3808_; 
v___x_3807_ = ((size_t)1ULL);
v___x_3808_ = lean_usize_add(v_i_3792_, v___x_3807_);
v_i_3792_ = v___x_3808_;
v_b_3793_ = v___x_3806_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3931_, lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
size_t v_sz_boxed_3937_; size_t v_i_boxed_3938_; lean_object* v_res_3939_; 
v_sz_boxed_3937_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3938_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3931_, v_sz_boxed_3937_, v_i_boxed_3938_, v_b_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v_as_3931_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3940_, size_t v_sz_3941_, size_t v_i_3942_, lean_object* v_b_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
uint8_t v___x_3949_; 
v___x_3949_ = lean_usize_dec_lt(v_i_3942_, v_sz_3941_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v_b_3943_);
return v___x_3950_;
}
else
{
lean_object* v_snd_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_4082_; 
v_snd_3951_ = lean_ctor_get(v_b_3943_, 1);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_b_3943_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; 
v_unused_4083_ = lean_ctor_get(v_b_3943_, 0);
lean_dec(v_unused_4083_);
v___x_3953_ = v_b_3943_;
v_isShared_3954_ = v_isSharedCheck_4082_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_snd_3951_);
lean_dec(v_b_3943_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_4082_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; lean_object* v_a_3957_; lean_object* v_a_3964_; 
v___x_3955_ = lean_box(0);
v_a_3964_ = lean_array_uget_borrowed(v_as_3940_, v_i_3942_);
if (lean_obj_tag(v_a_3964_) == 0)
{
v_a_3957_ = v_snd_3951_;
goto v___jp_3956_;
}
else
{
lean_object* v_val_3965_; uint8_t v_a_3967_; lean_object* v___f_3970_; lean_object* v___f_3971_; 
v_val_3965_ = lean_ctor_get(v_a_3964_, 0);
v___f_3970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3951_);
v___f_3971_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3971_, 0, v_snd_3951_);
if (lean_obj_tag(v_val_3965_) == 0)
{
lean_object* v_type_3972_; lean_object* v___x_3973_; uint8_t v_fst_3975_; lean_object* v_mctx_3976_; lean_object* v___y_3992_; lean_object* v_mctx_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v_type_3972_ = lean_ctor_get(v_val_3965_, 3);
v___x_3973_ = lean_st_ref_get(v___y_3945_);
v_mctx_3997_ = lean_ctor_get(v___x_3973_, 0);
lean_inc_ref_n(v_mctx_3997_, 2);
lean_dec(v___x_3973_);
v___x_3998_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
lean_ctor_set(v___x_3999_, 1, v_mctx_3997_);
v___x_4000_ = l_Lean_Expr_hasFVar(v_type_3972_);
if (v___x_4000_ == 0)
{
uint8_t v___x_4001_; 
v___x_4001_ = l_Lean_Expr_hasMVar(v_type_3972_);
if (v___x_4001_ == 0)
{
lean_dec_ref_known(v___x_3999_, 2);
lean_dec_ref(v___f_3971_);
v_fst_3975_ = v___x_4001_;
v_mctx_3976_ = v_mctx_3997_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_4002_; 
lean_dec_ref(v_mctx_3997_);
lean_inc_ref(v_type_3972_);
v___x_4002_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_3972_, v___x_3999_);
v___y_3992_ = v___x_4002_;
goto v___jp_3991_;
}
}
else
{
lean_object* v___x_4003_; 
lean_dec_ref(v_mctx_3997_);
lean_inc_ref(v_type_3972_);
v___x_4003_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_3972_, v___x_3999_);
v___y_3992_ = v___x_4003_;
goto v___jp_3991_;
}
v___jp_3974_:
{
lean_object* v___x_3977_; lean_object* v_cache_3978_; lean_object* v_zetaDeltaFVarIds_3979_; lean_object* v_postponed_3980_; lean_object* v_diag_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3989_; 
v___x_3977_ = lean_st_ref_take(v___y_3945_);
v_cache_3978_ = lean_ctor_get(v___x_3977_, 1);
v_zetaDeltaFVarIds_3979_ = lean_ctor_get(v___x_3977_, 2);
v_postponed_3980_ = lean_ctor_get(v___x_3977_, 3);
v_diag_3981_ = lean_ctor_get(v___x_3977_, 4);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v___x_3977_, 0);
lean_dec(v_unused_3990_);
v___x_3983_ = v___x_3977_;
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_diag_3981_);
lean_inc(v_postponed_3980_);
lean_inc(v_zetaDeltaFVarIds_3979_);
lean_inc(v_cache_3978_);
lean_dec(v___x_3977_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v_mctx_3976_);
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_mctx_3976_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v_cache_3978_);
lean_ctor_set(v_reuseFailAlloc_3988_, 2, v_zetaDeltaFVarIds_3979_);
lean_ctor_set(v_reuseFailAlloc_3988_, 3, v_postponed_3980_);
lean_ctor_set(v_reuseFailAlloc_3988_, 4, v_diag_3981_);
v___x_3986_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_st_ref_put(v___y_3945_, v___x_3986_);
v_a_3967_ = v_fst_3975_;
goto v___jp_3966_;
}
}
}
v___jp_3991_:
{
lean_object* v_snd_3993_; lean_object* v_fst_3994_; lean_object* v_mctx_3995_; uint8_t v___x_3996_; 
v_snd_3993_ = lean_ctor_get(v___y_3992_, 1);
lean_inc(v_snd_3993_);
v_fst_3994_ = lean_ctor_get(v___y_3992_, 0);
lean_inc(v_fst_3994_);
lean_dec_ref(v___y_3992_);
v_mctx_3995_ = lean_ctor_get(v_snd_3993_, 1);
lean_inc_ref(v_mctx_3995_);
lean_dec(v_snd_3993_);
v___x_3996_ = lean_unbox(v_fst_3994_);
lean_dec(v_fst_3994_);
v_fst_3975_ = v___x_3996_;
v_mctx_3976_ = v_mctx_3995_;
goto v___jp_3974_;
}
}
else
{
uint8_t v_nondep_4004_; 
v_nondep_4004_ = lean_ctor_get_uint8(v_val_3965_, sizeof(void*)*5);
if (v_nondep_4004_ == 0)
{
lean_object* v_type_4005_; lean_object* v_value_4006_; lean_object* v___x_4007_; uint8_t v_fst_4009_; lean_object* v_snd_4010_; lean_object* v___y_4027_; uint8_t v_fst_4032_; lean_object* v_snd_4033_; lean_object* v___y_4039_; lean_object* v_mctx_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v_type_4005_ = lean_ctor_get(v_val_3965_, 3);
v_value_4006_ = lean_ctor_get(v_val_3965_, 4);
v___x_4007_ = lean_st_ref_get(v___y_3945_);
v_mctx_4043_ = lean_ctor_get(v___x_4007_, 0);
lean_inc_ref(v_mctx_4043_);
lean_dec(v___x_4007_);
v___x_4044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
lean_ctor_set(v___x_4045_, 1, v_mctx_4043_);
v___x_4046_ = l_Lean_Expr_hasFVar(v_type_4005_);
if (v___x_4046_ == 0)
{
uint8_t v___x_4047_; 
v___x_4047_ = l_Lean_Expr_hasMVar(v_type_4005_);
if (v___x_4047_ == 0)
{
v_fst_4032_ = v___x_4047_;
v_snd_4033_ = v___x_4045_;
goto v___jp_4031_;
}
else
{
lean_object* v___x_4048_; 
lean_inc_ref(v_type_4005_);
lean_inc_ref(v___f_3971_);
v___x_4048_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_4005_, v___x_4045_);
v___y_4039_ = v___x_4048_;
goto v___jp_4038_;
}
}
else
{
lean_object* v___x_4049_; 
lean_inc_ref(v_type_4005_);
lean_inc_ref(v___f_3971_);
v___x_4049_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_4005_, v___x_4045_);
v___y_4039_ = v___x_4049_;
goto v___jp_4038_;
}
v___jp_4008_:
{
lean_object* v_mctx_4011_; lean_object* v___x_4012_; lean_object* v_cache_4013_; lean_object* v_zetaDeltaFVarIds_4014_; lean_object* v_postponed_4015_; lean_object* v_diag_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4024_; 
v_mctx_4011_ = lean_ctor_get(v_snd_4010_, 1);
lean_inc_ref(v_mctx_4011_);
lean_dec_ref(v_snd_4010_);
v___x_4012_ = lean_st_ref_take(v___y_3945_);
v_cache_4013_ = lean_ctor_get(v___x_4012_, 1);
v_zetaDeltaFVarIds_4014_ = lean_ctor_get(v___x_4012_, 2);
v_postponed_4015_ = lean_ctor_get(v___x_4012_, 3);
v_diag_4016_ = lean_ctor_get(v___x_4012_, 4);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v___x_4012_, 0);
lean_dec(v_unused_4025_);
v___x_4018_ = v___x_4012_;
v_isShared_4019_ = v_isSharedCheck_4024_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_diag_4016_);
lean_inc(v_postponed_4015_);
lean_inc(v_zetaDeltaFVarIds_4014_);
lean_inc(v_cache_4013_);
lean_dec(v___x_4012_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4024_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v_mctx_4011_);
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_mctx_4011_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_cache_4013_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v_zetaDeltaFVarIds_4014_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v_postponed_4015_);
lean_ctor_set(v_reuseFailAlloc_4023_, 4, v_diag_4016_);
v___x_4021_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_st_ref_put(v___y_3945_, v___x_4021_);
v_a_3967_ = v_fst_4009_;
goto v___jp_3966_;
}
}
}
v___jp_4026_:
{
lean_object* v_fst_4028_; lean_object* v_snd_4029_; uint8_t v___x_4030_; 
v_fst_4028_ = lean_ctor_get(v___y_4027_, 0);
lean_inc(v_fst_4028_);
v_snd_4029_ = lean_ctor_get(v___y_4027_, 1);
lean_inc(v_snd_4029_);
lean_dec_ref(v___y_4027_);
v___x_4030_ = lean_unbox(v_fst_4028_);
lean_dec(v_fst_4028_);
v_fst_4009_ = v___x_4030_;
v_snd_4010_ = v_snd_4029_;
goto v___jp_4008_;
}
v___jp_4031_:
{
if (v_fst_4032_ == 0)
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Lean_Expr_hasFVar(v_value_4006_);
if (v___x_4034_ == 0)
{
uint8_t v___x_4035_; 
v___x_4035_ = l_Lean_Expr_hasMVar(v_value_4006_);
if (v___x_4035_ == 0)
{
lean_dec_ref(v___f_3971_);
v_fst_4009_ = v___x_4035_;
v_snd_4010_ = v_snd_4033_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4036_; 
lean_inc_ref(v_value_4006_);
v___x_4036_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_value_4006_, v_snd_4033_);
v___y_4027_ = v___x_4036_;
goto v___jp_4026_;
}
}
else
{
lean_object* v___x_4037_; 
lean_inc_ref(v_value_4006_);
v___x_4037_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_value_4006_, v_snd_4033_);
v___y_4027_ = v___x_4037_;
goto v___jp_4026_;
}
}
else
{
lean_dec_ref(v___f_3971_);
v_fst_4009_ = v_fst_4032_;
v_snd_4010_ = v_snd_4033_;
goto v___jp_4008_;
}
}
v___jp_4038_:
{
lean_object* v_fst_4040_; lean_object* v_snd_4041_; uint8_t v___x_4042_; 
v_fst_4040_ = lean_ctor_get(v___y_4039_, 0);
lean_inc(v_fst_4040_);
v_snd_4041_ = lean_ctor_get(v___y_4039_, 1);
lean_inc(v_snd_4041_);
lean_dec_ref(v___y_4039_);
v___x_4042_ = lean_unbox(v_fst_4040_);
lean_dec(v_fst_4040_);
v_fst_4032_ = v___x_4042_;
v_snd_4033_ = v_snd_4041_;
goto v___jp_4031_;
}
}
else
{
lean_object* v_type_4050_; lean_object* v___x_4051_; uint8_t v_fst_4053_; lean_object* v_mctx_4054_; lean_object* v___y_4070_; lean_object* v_mctx_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_type_4050_ = lean_ctor_get(v_val_3965_, 3);
v___x_4051_ = lean_st_ref_get(v___y_3945_);
v_mctx_4075_ = lean_ctor_get(v___x_4051_, 0);
lean_inc_ref_n(v_mctx_4075_, 2);
lean_dec(v___x_4051_);
v___x_4076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v_mctx_4075_);
v___x_4078_ = l_Lean_Expr_hasFVar(v_type_4050_);
if (v___x_4078_ == 0)
{
uint8_t v___x_4079_; 
v___x_4079_ = l_Lean_Expr_hasMVar(v_type_4050_);
if (v___x_4079_ == 0)
{
lean_dec_ref_known(v___x_4077_, 2);
lean_dec_ref(v___f_3971_);
v_fst_4053_ = v___x_4079_;
v_mctx_4054_ = v_mctx_4075_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4080_; 
lean_dec_ref(v_mctx_4075_);
lean_inc_ref(v_type_4050_);
v___x_4080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_4050_, v___x_4077_);
v___y_4070_ = v___x_4080_;
goto v___jp_4069_;
}
}
else
{
lean_object* v___x_4081_; 
lean_dec_ref(v_mctx_4075_);
lean_inc_ref(v_type_4050_);
v___x_4081_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3971_, v___f_3970_, v_type_4050_, v___x_4077_);
v___y_4070_ = v___x_4081_;
goto v___jp_4069_;
}
v___jp_4052_:
{
lean_object* v___x_4055_; lean_object* v_cache_4056_; lean_object* v_zetaDeltaFVarIds_4057_; lean_object* v_postponed_4058_; lean_object* v_diag_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4067_; 
v___x_4055_ = lean_st_ref_take(v___y_3945_);
v_cache_4056_ = lean_ctor_get(v___x_4055_, 1);
v_zetaDeltaFVarIds_4057_ = lean_ctor_get(v___x_4055_, 2);
v_postponed_4058_ = lean_ctor_get(v___x_4055_, 3);
v_diag_4059_ = lean_ctor_get(v___x_4055_, 4);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v___x_4055_, 0);
lean_dec(v_unused_4068_);
v___x_4061_ = v___x_4055_;
v_isShared_4062_ = v_isSharedCheck_4067_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_diag_4059_);
lean_inc(v_postponed_4058_);
lean_inc(v_zetaDeltaFVarIds_4057_);
lean_inc(v_cache_4056_);
lean_dec(v___x_4055_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4067_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v_mctx_4054_);
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_mctx_4054_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_cache_4056_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v_zetaDeltaFVarIds_4057_);
lean_ctor_set(v_reuseFailAlloc_4066_, 3, v_postponed_4058_);
lean_ctor_set(v_reuseFailAlloc_4066_, 4, v_diag_4059_);
v___x_4064_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_st_ref_put(v___y_3945_, v___x_4064_);
v_a_3967_ = v_fst_4053_;
goto v___jp_3966_;
}
}
}
v___jp_4069_:
{
lean_object* v_snd_4071_; lean_object* v_fst_4072_; lean_object* v_mctx_4073_; uint8_t v___x_4074_; 
v_snd_4071_ = lean_ctor_get(v___y_4070_, 1);
lean_inc(v_snd_4071_);
v_fst_4072_ = lean_ctor_get(v___y_4070_, 0);
lean_inc(v_fst_4072_);
lean_dec_ref(v___y_4070_);
v_mctx_4073_ = lean_ctor_get(v_snd_4071_, 1);
lean_inc_ref(v_mctx_4073_);
lean_dec(v_snd_4071_);
v___x_4074_ = lean_unbox(v_fst_4072_);
lean_dec(v_fst_4072_);
v_fst_4053_ = v___x_4074_;
v_mctx_4054_ = v_mctx_4073_;
goto v___jp_4052_;
}
}
}
v___jp_3966_:
{
if (v_a_3967_ == 0)
{
v_a_3957_ = v_snd_3951_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = l_Lean_LocalDecl_fvarId(v_val_3965_);
v___x_3969_ = lean_array_push(v_snd_3951_, v___x_3968_);
v_a_3957_ = v___x_3969_;
goto v___jp_3956_;
}
}
}
v___jp_3956_:
{
lean_object* v___x_3959_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v_a_3957_);
lean_ctor_set(v___x_3953_, 0, v___x_3955_);
v___x_3959_ = v___x_3953_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_a_3957_);
v___x_3959_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = ((size_t)1ULL);
v___x_3961_ = lean_usize_add(v_i_3942_, v___x_3960_);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3940_, v_sz_3941_, v___x_3961_, v___x_3959_, v___y_3945_);
return v___x_3962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4084_, lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
size_t v_sz_boxed_4093_; size_t v_i_boxed_4094_; lean_object* v_res_4095_; 
v_sz_boxed_4093_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4094_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4084_, v_sz_boxed_4093_, v_i_boxed_4094_, v_b_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec_ref(v_as_4084_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4096_, lean_object* v_init_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_root_4103_; lean_object* v_tail_4104_; lean_object* v___x_4105_; 
v_root_4103_ = lean_ctor_get(v_t_4096_, 0);
v_tail_4104_ = lean_ctor_get(v_t_4096_, 1);
lean_inc_ref(v_init_4097_);
v___x_4105_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4097_, v_root_4103_, v_init_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec_ref(v_init_4097_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4142_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4142_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4142_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
if (lean_obj_tag(v_a_4106_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4112_; 
v_a_4110_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v_a_4106_, 1);
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v_a_4110_);
v___x_4112_ = v___x_4108_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; size_t v_sz_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
lean_del_object(v___x_4108_);
v_a_4114_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v_a_4106_, 1);
v___x_4115_ = lean_box(0);
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v_a_4114_);
v_sz_4117_ = lean_array_size(v_tail_4104_);
v___x_4118_ = ((size_t)0ULL);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4104_, v_sz_4117_, v___x_4118_, v___x_4116_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4133_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v_fst_4124_; 
v_fst_4124_ = lean_ctor_get(v_a_4120_, 0);
if (lean_obj_tag(v_fst_4124_) == 0)
{
lean_object* v_snd_4125_; lean_object* v___x_4127_; 
v_snd_4125_ = lean_ctor_get(v_a_4120_, 1);
lean_inc(v_snd_4125_);
lean_dec(v_a_4120_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v_snd_4125_);
v___x_4127_ = v___x_4122_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_snd_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
else
{
lean_object* v_val_4129_; lean_object* v___x_4131_; 
lean_inc_ref(v_fst_4124_);
lean_dec(v_a_4120_);
v_val_4129_ = lean_ctor_get(v_fst_4124_, 0);
lean_inc(v_val_4129_);
lean_dec_ref_known(v_fst_4124_, 1);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v_val_4129_);
v___x_4131_ = v___x_4122_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_val_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_a_4134_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4119_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4119_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_a_4143_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4105_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4105_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4151_, lean_object* v_init_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4151_, v_init_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_t_4151_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4159_, lean_object* v_fvarIds_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v___x_4166_; 
lean_inc(v_goal_4159_);
v___x_4166_ = l_Lean_MVarId_getDecl(v_goal_4159_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v_lctx_4168_; lean_object* v_decls_4169_; lean_object* v___x_4170_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v_lctx_4168_ = lean_ctor_get(v_a_4167_, 1);
lean_inc_ref(v_lctx_4168_);
lean_dec(v_a_4167_);
v_decls_4169_ = lean_ctor_get(v_lctx_4168_, 1);
lean_inc_ref(v_decls_4169_);
lean_dec_ref(v_lctx_4168_);
v___x_4170_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4169_, v_fvarIds_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec_ref(v_decls_4169_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___x_4172_ = l_Lean_MVarId_tryClearMany(v_goal_4159_, v_a_4171_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4171_);
return v___x_4172_;
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v_goal_4159_);
v_a_4173_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4170_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4170_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref(v_fvarIds_4160_);
lean_dec(v_goal_4159_);
v_a_4181_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4166_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4166_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4189_, lean_object* v_fvarIds_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4189_, v_fvarIds_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4197_, size_t v_sz_4198_, size_t v_i_4199_, lean_object* v_b_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4197_, v_sz_4198_, v_i_4199_, v_b_4200_, v___y_4202_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4207_, lean_object* v_sz_4208_, lean_object* v_i_4209_, lean_object* v_b_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
size_t v_sz_boxed_4216_; size_t v_i_boxed_4217_; lean_object* v_res_4218_; 
v_sz_boxed_4216_ = lean_unbox_usize(v_sz_4208_);
lean_dec(v_sz_4208_);
v_i_boxed_4217_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4207_, v_sz_boxed_4216_, v_i_boxed_4217_, v_b_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_as_4207_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4219_, size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_b_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4219_, v_sz_4220_, v_i_4221_, v_b_4222_, v___y_4224_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4229_, lean_object* v_sz_4230_, lean_object* v_i_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
size_t v_sz_boxed_4238_; size_t v_i_boxed_4239_; lean_object* v_res_4240_; 
v_sz_boxed_4238_ = lean_unbox_usize(v_sz_4230_);
lean_dec(v_sz_4230_);
v_i_boxed_4239_ = lean_unbox_usize(v_i_4231_);
lean_dec(v_i_4231_);
v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4229_, v_sz_boxed_4238_, v_i_boxed_4239_, v_b_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_as_4229_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4241_, lean_object* v_as_4242_, size_t v_sz_4243_, size_t v_i_4244_, lean_object* v_b_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
uint8_t v___x_4253_; 
v___x_4253_ = lean_usize_dec_lt(v_i_4244_, v_sz_4243_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v_b_4245_);
return v___x_4254_;
}
else
{
lean_object* v_a_4255_; lean_object* v_fst_4256_; lean_object* v_snd_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_a_4255_ = lean_array_uget_borrowed(v_as_4242_, v_i_4244_);
v_fst_4256_ = lean_ctor_get(v_a_4255_, 0);
v_snd_4257_ = lean_ctor_get(v_a_4255_, 1);
v___x_4258_ = lean_box(0);
lean_inc(v_snd_4257_);
v___x_4259_ = l_Lean_Meta_FVarSubst_get(v_fs_4241_, v_snd_4257_);
lean_inc(v_fst_4256_);
v___x_4260_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4256_, v___x_4259_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4260_) == 0)
{
size_t v___x_4261_; size_t v___x_4262_; 
lean_dec_ref_known(v___x_4260_, 1);
v___x_4261_ = ((size_t)1ULL);
v___x_4262_ = lean_usize_add(v_i_4244_, v___x_4261_);
v_i_4244_ = v___x_4262_;
v_b_4245_ = v___x_4258_;
goto _start;
}
else
{
return v___x_4260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4264_, lean_object* v_as_4265_, lean_object* v_sz_4266_, lean_object* v_i_4267_, lean_object* v_b_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4266_);
lean_dec(v_sz_4266_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4267_);
lean_dec(v_i_4267_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4264_, v_as_4265_, v_sz_boxed_4276_, v_i_boxed_4277_, v_b_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v_as_4265_);
lean_dec(v_fs_4264_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4279_, lean_object* v_toTag_4280_, size_t v_sz_4281_, size_t v___x_4282_, lean_object* v___x_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4279_, v_toTag_4280_, v_sz_4281_, v___x_4282_, v___x_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; 
v_unused_4299_ = lean_ctor_get(v___x_4291_, 0);
lean_dec(v_unused_4299_);
v___x_4293_ = v___x_4291_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_dec(v___x_4291_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4283_);
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4283_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
else
{
return v___x_4291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4300_, lean_object* v_toTag_4301_, lean_object* v_sz_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
size_t v_sz_boxed_4312_; size_t v___x_1634__boxed_4313_; lean_object* v_res_4314_; 
v_sz_boxed_4312_ = lean_unbox_usize(v_sz_4302_);
lean_dec(v_sz_4302_);
v___x_1634__boxed_4313_ = lean_unbox_usize(v___x_4303_);
lean_dec(v___x_4303_);
v_res_4314_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4300_, v_toTag_4301_, v_sz_boxed_4312_, v___x_1634__boxed_4313_, v___x_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_toTag_4301_);
lean_dec(v_fs_4300_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4315_, size_t v_i_4316_, size_t v_stop_4317_, lean_object* v_b_4318_){
_start:
{
lean_object* v___y_4320_; uint8_t v___x_4324_; 
v___x_4324_ = lean_usize_dec_eq(v_i_4316_, v_stop_4317_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_array_uget_borrowed(v_as_4315_, v_i_4316_);
v___x_4326_ = l_Lean_Expr_isFVar(v___x_4325_);
if (v___x_4326_ == 0)
{
v___y_4320_ = v_b_4318_;
goto v___jp_4319_;
}
else
{
lean_object* v___x_4327_; 
lean_inc(v___x_4325_);
v___x_4327_ = lean_array_push(v_b_4318_, v___x_4325_);
v___y_4320_ = v___x_4327_;
goto v___jp_4319_;
}
}
else
{
return v_b_4318_;
}
v___jp_4319_:
{
size_t v___x_4321_; size_t v___x_4322_; 
v___x_4321_ = ((size_t)1ULL);
v___x_4322_ = lean_usize_add(v_i_4316_, v___x_4321_);
v_i_4316_ = v___x_4322_;
v_b_4318_ = v___y_4320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4328_, lean_object* v_i_4329_, lean_object* v_stop_4330_, lean_object* v_b_4331_){
_start:
{
size_t v_i_boxed_4332_; size_t v_stop_boxed_4333_; lean_object* v_res_4334_; 
v_i_boxed_4332_ = lean_unbox_usize(v_i_4329_);
lean_dec(v_i_4329_);
v_stop_boxed_4333_ = lean_unbox_usize(v_stop_4330_);
lean_dec(v_stop_4330_);
v_res_4334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4328_, v_i_boxed_4332_, v_stop_boxed_4333_, v_b_4331_);
lean_dec_ref(v_as_4328_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4335_, size_t v_sz_4336_, size_t v_i_4337_, lean_object* v_bs_4338_){
_start:
{
uint8_t v___x_4339_; 
v___x_4339_ = lean_usize_dec_lt(v_i_4337_, v_sz_4336_);
if (v___x_4339_ == 0)
{
return v_bs_4338_;
}
else
{
lean_object* v_v_4340_; lean_object* v___x_4341_; lean_object* v_bs_x27_4342_; lean_object* v___x_4343_; size_t v___x_4344_; size_t v___x_4345_; lean_object* v___x_4346_; 
v_v_4340_ = lean_array_uget(v_bs_4338_, v_i_4337_);
v___x_4341_ = lean_unsigned_to_nat(0u);
v_bs_x27_4342_ = lean_array_uset(v_bs_4338_, v_i_4337_, v___x_4341_);
v___x_4343_ = l_Lean_Meta_FVarSubst_get(v_fs_4335_, v_v_4340_);
v___x_4344_ = ((size_t)1ULL);
v___x_4345_ = lean_usize_add(v_i_4337_, v___x_4344_);
v___x_4346_ = lean_array_uset(v_bs_x27_4342_, v_i_4337_, v___x_4343_);
v_i_4337_ = v___x_4345_;
v_bs_4338_ = v___x_4346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4348_, lean_object* v_sz_4349_, lean_object* v_i_4350_, lean_object* v_bs_4351_){
_start:
{
size_t v_sz_boxed_4352_; size_t v_i_boxed_4353_; lean_object* v_res_4354_; 
v_sz_boxed_4352_ = lean_unbox_usize(v_sz_4349_);
lean_dec(v_sz_4349_);
v_i_boxed_4353_ = lean_unbox_usize(v_i_4350_);
lean_dec(v_i_4350_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4348_, v_sz_boxed_4352_, v_i_boxed_4353_, v_bs_4351_);
lean_dec(v_fs_4348_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_bs_4357_){
_start:
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_usize_dec_lt(v_i_4356_, v_sz_4355_);
if (v___x_4358_ == 0)
{
return v_bs_4357_;
}
else
{
lean_object* v_v_4359_; lean_object* v___x_4360_; lean_object* v_bs_x27_4361_; lean_object* v___x_4362_; size_t v___x_4363_; size_t v___x_4364_; lean_object* v___x_4365_; 
v_v_4359_ = lean_array_uget(v_bs_4357_, v_i_4356_);
v___x_4360_ = lean_unsigned_to_nat(0u);
v_bs_x27_4361_ = lean_array_uset(v_bs_4357_, v_i_4356_, v___x_4360_);
v___x_4362_ = l_Lean_Expr_fvarId_x21(v_v_4359_);
lean_dec(v_v_4359_);
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4356_, v___x_4363_);
v___x_4365_ = lean_array_uset(v_bs_x27_4361_, v_i_4356_, v___x_4362_);
v_i_4356_ = v___x_4364_;
v_bs_4357_ = v___x_4365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4367_, lean_object* v_i_4368_, lean_object* v_bs_4369_){
_start:
{
size_t v_sz_boxed_4370_; size_t v_i_boxed_4371_; lean_object* v_res_4372_; 
v_sz_boxed_4370_ = lean_unbox_usize(v_sz_4367_);
lean_dec(v_sz_4367_);
v_i_boxed_4371_ = lean_unbox_usize(v_i_4368_);
lean_dec(v_i_4368_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4370_, v_i_boxed_4371_, v_bs_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4377_, lean_object* v_g_4378_, lean_object* v_fs_4379_, lean_object* v_clears_4380_, lean_object* v_gs_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v___y_4390_; size_t v_sz_4427_; size_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v_sz_4427_ = lean_array_size(v_clears_4380_);
v___x_4428_ = ((size_t)0ULL);
v___x_4429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4379_, v_sz_4427_, v___x_4428_, v_clears_4380_);
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = lean_array_get_size(v___x_4429_);
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4433_ = lean_nat_dec_lt(v___x_4430_, v___x_4431_);
if (v___x_4433_ == 0)
{
lean_dec_ref(v___x_4429_);
v___y_4390_ = v___x_4432_;
goto v___jp_4389_;
}
else
{
uint8_t v___x_4434_; 
v___x_4434_ = lean_nat_dec_le(v___x_4431_, v___x_4431_);
if (v___x_4434_ == 0)
{
if (v___x_4433_ == 0)
{
lean_dec_ref(v___x_4429_);
v___y_4390_ = v___x_4432_;
goto v___jp_4389_;
}
else
{
size_t v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_usize_of_nat(v___x_4431_);
v___x_4436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4429_, v___x_4428_, v___x_4435_, v___x_4432_);
lean_dec_ref(v___x_4429_);
v___y_4390_ = v___x_4436_;
goto v___jp_4389_;
}
}
else
{
size_t v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = lean_usize_of_nat(v___x_4431_);
v___x_4438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4429_, v___x_4428_, v___x_4437_, v___x_4432_);
lean_dec_ref(v___x_4429_);
v___y_4390_ = v___x_4438_;
goto v___jp_4389_;
}
}
v___jp_4389_:
{
size_t v_sz_4391_; size_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_sz_4391_ = lean_array_size(v___y_4390_);
v___x_4392_ = ((size_t)0ULL);
v___x_4393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4391_, v___x_4392_, v___y_4390_);
v___x_4394_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4378_, v___x_4393_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; size_t v_sz_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; lean_object* v___x_4401_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc_n(v_a_4395_, 2);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = lean_box(0);
v_sz_4397_ = lean_array_size(v_toTag_4377_);
v___x_4398_ = lean_box_usize(v_sz_4397_);
v___x_4399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4400_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4400_, 0, v_fs_4379_);
lean_closure_set(v___f_4400_, 1, v_toTag_4377_);
lean_closure_set(v___f_4400_, 2, v___x_4398_);
lean_closure_set(v___f_4400_, 3, v___x_4399_);
lean_closure_set(v___f_4400_, 4, v___x_4396_);
v___x_4401_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4395_, v___f_4400_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4409_; 
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; 
v_unused_4410_ = lean_ctor_get(v___x_4401_, 0);
lean_dec(v_unused_4410_);
v___x_4403_ = v___x_4401_;
v_isShared_4404_ = v_isSharedCheck_4409_;
goto v_resetjp_4402_;
}
else
{
lean_dec(v___x_4401_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4409_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4405_ = lean_array_push(v_gs_4381_, v_a_4395_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4405_);
v___x_4407_ = v___x_4403_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4395_);
lean_dec_ref(v_gs_4381_);
v_a_4411_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4401_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4401_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_gs_4381_);
lean_dec(v_fs_4379_);
lean_dec_ref(v_toTag_4377_);
v_a_4419_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4394_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4394_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4439_, lean_object* v_g_4440_, lean_object* v_fs_4441_, lean_object* v_clears_4442_, lean_object* v_gs_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4439_, v_g_4440_, v_fs_4441_, v_clears_4442_, v_gs_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
return v_res_4451_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = lean_box(0);
v___x_4453_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
lean_ctor_set(v___x_4454_, 1, v___x_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4512_);
v___x_4519_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4512_);
v___x_4521_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4512_);
v___x_4523_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4524_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4512_);
v___x_4525_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4512_);
v___x_4527_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4512_);
v___x_4529_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___x_4530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4512_);
v___x_4531_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4530_);
if (v___x_4531_ == 0)
{
lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4512_);
v___x_4533_ = l_Lean_Syntax_isOfKind(v_stx_4512_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_dec(v_stx_4512_);
v___x_4534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4534_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_unsigned_to_nat(1u);
v___x_4536_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4535_);
v___x_4537_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4536_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4546_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4546_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4546_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4542_, 0, v_stx_4512_);
lean_ctor_set(v___x_4542_, 1, v_a_4538_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4542_);
v___x_4544_ = v___x_4540_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
else
{
lean_dec(v_stx_4512_);
return v___x_4537_;
}
}
}
else
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v_ps_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4547_ = lean_unsigned_to_nat(1u);
v___x_4548_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4547_);
v_ps_4549_ = l_Lean_Syntax_getArgs(v___x_4548_);
lean_dec(v___x_4548_);
v___x_4550_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4549_);
lean_dec_ref(v_ps_4549_);
v___x_4551_ = lean_array_to_list(v___x_4550_);
v___x_4552_ = lean_box(0);
v___x_4553_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4551_, v___x_4552_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4556_ = v___x_4553_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4553_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4558_, 0, v_stx_4512_);
lean_ctor_set(v___x_4558_, 1, v_a_4554_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 0, v___x_4558_);
v___x_4560_ = v___x_4556_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4558_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_stx_4512_);
v_a_4563_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4553_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4553_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
else
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = lean_unsigned_to_nat(1u);
v___x_4572_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4571_);
v___x_4573_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4572_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4582_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4582_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4582_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4578_, 0, v_stx_4512_);
lean_ctor_set(v___x_4578_, 1, v_a_4574_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4578_);
v___x_4580_ = v___x_4576_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
else
{
lean_dec(v_stx_4512_);
return v___x_4573_;
}
}
}
else
{
lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4583_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4583_, 0, v_stx_4512_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
else
{
lean_object* v___x_4585_; lean_object* v_h_4586_; 
v___x_4585_ = lean_unsigned_to_nat(0u);
v_h_4586_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4585_);
lean_dec(v_stx_4512_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4586_);
v___x_4592_ = l_Lean_Syntax_isOfKind(v_h_4586_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
lean_dec(v_h_4586_);
v___x_4593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4593_;
}
else
{
goto v___jp_4587_;
}
}
else
{
goto v___jp_4587_;
}
v___jp_4587_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = l_Lean_TSyntax_getId(v_h_4586_);
v___x_4589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4589_, 0, v_h_4586_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
return v___x_4590_;
}
}
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4595_, 0, v_stx_4512_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
else
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4597_);
if (v___x_4519_ == 0)
{
uint8_t v___x_4618_; 
lean_inc(v___x_4598_);
v___x_4618_ = l_Lean_Syntax_isOfKind(v___x_4598_, v___x_4518_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; 
lean_dec(v___x_4598_);
lean_dec(v_stx_4512_);
v___x_4619_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4619_;
}
else
{
goto v___jp_4599_;
}
}
else
{
goto v___jp_4599_;
}
v___jp_4599_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4600_ = lean_unsigned_to_nat(1u);
v___x_4601_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4600_);
v___x_4602_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4601_);
v___x_4603_ = l_Lean_Syntax_matchesNull(v___x_4601_, v___x_4602_);
if (v___x_4603_ == 0)
{
uint8_t v___x_4604_; 
lean_dec(v_stx_4512_);
v___x_4604_ = l_Lean_Syntax_matchesNull(v___x_4601_, v___x_4597_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; 
lean_dec(v___x_4598_);
v___x_4605_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4605_;
}
else
{
v_stx_4512_ = v___x_4598_;
goto _start;
}
}
else
{
lean_object* v_t_4607_; lean_object* v___x_4608_; 
v_t_4607_ = l_Lean_Syntax_getArg(v___x_4601_, v___x_4600_);
lean_dec(v___x_4601_);
v___x_4608_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4598_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4611_ = v___x_4608_;
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4613_, 0, v_stx_4512_);
lean_ctor_set(v___x_4613_, 1, v_a_4609_);
lean_ctor_set(v___x_4613_, 2, v_t_4607_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4613_);
v___x_4615_ = v___x_4611_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4613_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
else
{
lean_dec(v_t_4607_);
lean_dec(v_stx_4512_);
return v___x_4608_;
}
}
}
}
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v_ps_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = l_Lean_Syntax_getArg(v_stx_4512_, v___x_4620_);
v_ps_4622_ = l_Lean_Syntax_getArgs(v___x_4621_);
lean_dec(v___x_4621_);
v___x_4623_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4622_);
lean_dec_ref(v_ps_4622_);
v___x_4624_ = lean_array_to_list(v___x_4623_);
v___x_4625_ = lean_box(0);
v___x_4626_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4624_, v___x_4625_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4635_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4635_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4635_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4631_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4512_, v_a_4627_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4631_);
v___x_4633_ = v___x_4629_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_stx_4512_);
v_a_4636_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4626_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4626_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4644_, lean_object* v_x_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
if (lean_obj_tag(v_x_4644_) == 0)
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = l_List_reverse___redArg(v_x_4645_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
else
{
lean_object* v_head_4653_; lean_object* v_tail_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4672_; 
v_head_4653_ = lean_ctor_get(v_x_4644_, 0);
v_tail_4654_ = lean_ctor_get(v_x_4644_, 1);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_x_4644_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4656_ = v_x_4644_;
v_isShared_4657_ = v_isSharedCheck_4672_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_tail_4654_);
lean_inc(v_head_4653_);
lean_dec(v_x_4644_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4672_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; 
v___x_4658_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4653_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref_known(v___x_4658_, 1);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 1, v_x_4645_);
lean_ctor_set(v___x_4656_, 0, v_a_4659_);
v___x_4661_ = v___x_4656_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4659_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_x_4645_);
v___x_4661_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
v_x_4644_ = v_tail_4654_;
v_x_4645_ = v___x_4661_;
goto _start;
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_del_object(v___x_4656_);
lean_dec(v_tail_4654_);
lean_dec(v_x_4645_);
v_a_4664_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4658_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4658_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4673_, lean_object* v_x_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4673_, v_x_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4688_, lean_object* v_as_4689_, size_t v_sz_4690_, size_t v_i_4691_, lean_object* v_b_4692_){
_start:
{
lean_object* v_a_4695_; uint8_t v___x_4699_; 
v___x_4699_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v_b_4692_);
return v___x_4700_;
}
else
{
lean_object* v_fst_4701_; lean_object* v_snd_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4724_; 
v_fst_4701_ = lean_ctor_get(v_b_4692_, 0);
v_snd_4702_ = lean_ctor_get(v_b_4692_, 1);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_b_4692_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4704_ = v_b_4692_;
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_snd_4702_);
lean_inc(v_fst_4701_);
lean_dec(v_b_4692_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v_a_4706_; lean_object* v_expr_4707_; lean_object* v_hName_x3f_4708_; lean_object* v___x_4709_; uint8_t v___y_4720_; uint8_t v___x_4723_; 
v_a_4706_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
v_expr_4707_ = lean_ctor_get(v_a_4706_, 0);
v_hName_x3f_4708_ = lean_ctor_get(v_a_4706_, 2);
v___x_4709_ = lean_box(0);
v___x_4723_ = l_Lean_Expr_isFVar(v_expr_4707_);
if (v___x_4723_ == 0)
{
v___y_4720_ = v___x_4723_;
goto v___jp_4719_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4708_) == 0)
{
v___y_4720_ = v___x_4723_;
goto v___jp_4719_;
}
else
{
goto v___jp_4710_;
}
}
v___jp_4710_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v___x_4711_ = lean_array_get_borrowed(v___x_4709_, v_fst_4688_, v_snd_4702_);
lean_inc(v___x_4711_);
v___x_4712_ = l_Lean_mkFVar(v___x_4711_);
v___x_4713_ = lean_array_push(v_fst_4701_, v___x_4712_);
v___x_4714_ = lean_unsigned_to_nat(1u);
v___x_4715_ = lean_nat_add(v_snd_4702_, v___x_4714_);
lean_dec(v_snd_4702_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 1, v___x_4715_);
lean_ctor_set(v___x_4704_, 0, v___x_4713_);
v___x_4717_ = v___x_4704_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
v_a_4695_ = v___x_4717_;
goto v___jp_4694_;
}
}
v___jp_4719_:
{
if (v___y_4720_ == 0)
{
goto v___jp_4710_;
}
else
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
lean_del_object(v___x_4704_);
lean_inc_ref(v_expr_4707_);
v___x_4721_ = lean_array_push(v_fst_4701_, v_expr_4707_);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
lean_ctor_set(v___x_4722_, 1, v_snd_4702_);
v_a_4695_ = v___x_4722_;
goto v___jp_4694_;
}
}
}
}
v___jp_4694_:
{
size_t v___x_4696_; size_t v___x_4697_; 
v___x_4696_ = ((size_t)1ULL);
v___x_4697_ = lean_usize_add(v_i_4691_, v___x_4696_);
v_i_4691_ = v___x_4697_;
v_b_4692_ = v_a_4695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4725_, lean_object* v_as_4726_, lean_object* v_sz_4727_, lean_object* v_i_4728_, lean_object* v_b_4729_, lean_object* v___y_4730_){
_start:
{
size_t v_sz_boxed_4731_; size_t v_i_boxed_4732_; lean_object* v_res_4733_; 
v_sz_boxed_4731_ = lean_unbox_usize(v_sz_4727_);
lean_dec(v_sz_4727_);
v_i_boxed_4732_ = lean_unbox_usize(v_i_4728_);
lean_dec(v_i_4728_);
v_res_4733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4725_, v_as_4726_, v_sz_boxed_4731_, v_i_boxed_4732_, v_b_4729_);
lean_dec_ref(v_as_4726_);
lean_dec_ref(v_fst_4725_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4734_, size_t v_i_4735_, size_t v_stop_4736_, lean_object* v_b_4737_){
_start:
{
lean_object* v___y_4739_; uint8_t v___x_4743_; 
v___x_4743_ = lean_usize_dec_eq(v_i_4735_, v_stop_4736_);
if (v___x_4743_ == 0)
{
lean_object* v___x_4744_; uint8_t v___y_4746_; lean_object* v_expr_4748_; lean_object* v_hName_x3f_4749_; uint8_t v___x_4750_; 
v___x_4744_ = lean_array_uget_borrowed(v_as_4734_, v_i_4735_);
v_expr_4748_ = lean_ctor_get(v___x_4744_, 0);
v_hName_x3f_4749_ = lean_ctor_get(v___x_4744_, 2);
v___x_4750_ = l_Lean_Expr_isFVar(v_expr_4748_);
if (v___x_4750_ == 0)
{
v___y_4746_ = v___x_4750_;
goto v___jp_4745_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4749_) == 0)
{
v___y_4746_ = v___x_4750_;
goto v___jp_4745_;
}
else
{
lean_object* v___x_4751_; 
lean_inc(v___x_4744_);
v___x_4751_ = lean_array_push(v_b_4737_, v___x_4744_);
v___y_4739_ = v___x_4751_;
goto v___jp_4738_;
}
}
v___jp_4745_:
{
if (v___y_4746_ == 0)
{
lean_object* v___x_4747_; 
lean_inc(v___x_4744_);
v___x_4747_ = lean_array_push(v_b_4737_, v___x_4744_);
v___y_4739_ = v___x_4747_;
goto v___jp_4738_;
}
else
{
v___y_4739_ = v_b_4737_;
goto v___jp_4738_;
}
}
}
else
{
return v_b_4737_;
}
v___jp_4738_:
{
size_t v___x_4740_; size_t v___x_4741_; 
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4735_, v___x_4740_);
v_i_4735_ = v___x_4741_;
v_b_4737_ = v___y_4739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4752_, lean_object* v_i_4753_, lean_object* v_stop_4754_, lean_object* v_b_4755_){
_start:
{
size_t v_i_boxed_4756_; size_t v_stop_boxed_4757_; lean_object* v_res_4758_; 
v_i_boxed_4756_ = lean_unbox_usize(v_i_4753_);
lean_dec(v_i_4753_);
v_stop_boxed_4757_ = lean_unbox_usize(v_stop_4754_);
lean_dec(v_stop_4754_);
v_res_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4752_, v_i_boxed_4756_, v_stop_boxed_4757_, v_b_4755_);
lean_dec_ref(v_as_4752_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4764_, lean_object* v_args_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___y_4772_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v_lower_4775_; lean_object* v_upper_4776_; lean_object* v_j_4782_; lean_object* v___y_4784_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_j_4782_ = lean_unsigned_to_nat(0u);
v___x_4815_ = lean_array_get_size(v_args_4765_);
v___x_4816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4817_ = lean_nat_dec_lt(v_j_4782_, v___x_4815_);
if (v___x_4817_ == 0)
{
v___y_4784_ = v___x_4816_;
goto v___jp_4783_;
}
else
{
uint8_t v___x_4818_; 
v___x_4818_ = lean_nat_dec_le(v___x_4815_, v___x_4815_);
if (v___x_4818_ == 0)
{
if (v___x_4817_ == 0)
{
v___y_4784_ = v___x_4816_;
goto v___jp_4783_;
}
else
{
size_t v___x_4819_; size_t v___x_4820_; lean_object* v___x_4821_; 
v___x_4819_ = ((size_t)0ULL);
v___x_4820_ = lean_usize_of_nat(v___x_4815_);
v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4765_, v___x_4819_, v___x_4820_, v___x_4816_);
v___y_4784_ = v___x_4821_;
goto v___jp_4783_;
}
}
else
{
size_t v___x_4822_; size_t v___x_4823_; lean_object* v___x_4824_; 
v___x_4822_ = ((size_t)0ULL);
v___x_4823_ = lean_usize_of_nat(v___x_4815_);
v___x_4824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4765_, v___x_4822_, v___x_4823_, v___x_4816_);
v___y_4784_ = v___x_4824_;
goto v___jp_4783_;
}
}
v___jp_4771_:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4777_ = l_Array_toSubarray___redArg(v___y_4772_, v_lower_4775_, v_upper_4776_);
v___x_4778_ = l_Subarray_copy___redArg(v___x_4777_);
v___x_4779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
lean_ctor_set(v___x_4779_, 1, v___y_4773_);
v___x_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___y_4774_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
return v___x_4781_;
}
v___jp_4783_:
{
uint8_t v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = 3;
v___x_4786_ = l_Lean_MVarId_generalize(v_goal_4764_, v___y_4784_, v___x_4785_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v_fst_4788_; lean_object* v_snd_4789_; lean_object* v___x_4790_; size_t v_sz_4791_; size_t v___x_4792_; lean_object* v___x_4793_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref_known(v___x_4786_, 1);
v_fst_4788_ = lean_ctor_get(v_a_4787_, 0);
lean_inc(v_fst_4788_);
v_snd_4789_ = lean_ctor_get(v_a_4787_, 1);
lean_inc(v_snd_4789_);
lean_dec(v_a_4787_);
v___x_4790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4791_ = lean_array_size(v_args_4765_);
v___x_4792_ = ((size_t)0ULL);
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4788_, v_args_4765_, v_sz_4791_, v___x_4792_, v___x_4790_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v_fst_4795_; lean_object* v_snd_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v_fst_4795_ = lean_ctor_get(v_a_4794_, 0);
lean_inc(v_fst_4795_);
v_snd_4796_ = lean_ctor_get(v_a_4794_, 1);
lean_inc(v_snd_4796_);
lean_dec(v_a_4794_);
v___x_4797_ = lean_array_get_size(v_fst_4788_);
v___x_4798_ = lean_nat_dec_le(v_snd_4796_, v_j_4782_);
if (v___x_4798_ == 0)
{
v___y_4772_ = v_fst_4788_;
v___y_4773_ = v_snd_4789_;
v___y_4774_ = v_fst_4795_;
v_lower_4775_ = v_snd_4796_;
v_upper_4776_ = v___x_4797_;
goto v___jp_4771_;
}
else
{
lean_dec(v_snd_4796_);
v___y_4772_ = v_fst_4788_;
v___y_4773_ = v_snd_4789_;
v___y_4774_ = v_fst_4795_;
v_lower_4775_ = v_j_4782_;
v_upper_4776_ = v___x_4797_;
goto v___jp_4771_;
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec(v_snd_4789_);
lean_dec(v_fst_4788_);
v_a_4799_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4793_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4793_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
v_a_4807_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4786_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4786_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4825_, lean_object* v_args_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4825_, v_args_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec_ref(v_args_4826_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4833_, lean_object* v_as_4834_, size_t v_sz_4835_, size_t v_i_4836_, lean_object* v_b_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4833_, v_as_4834_, v_sz_4835_, v_i_4836_, v_b_4837_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4844_, lean_object* v_as_4845_, lean_object* v_sz_4846_, lean_object* v_i_4847_, lean_object* v_b_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
size_t v_sz_boxed_4854_; size_t v_i_boxed_4855_; lean_object* v_res_4856_; 
v_sz_boxed_4854_ = lean_unbox_usize(v_sz_4846_);
lean_dec(v_sz_4846_);
v_i_boxed_4855_ = lean_unbox_usize(v_i_4847_);
lean_dec(v_i_4847_);
v_res_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4844_, v_as_4845_, v_sz_boxed_4854_, v_i_boxed_4855_, v_b_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v_as_4845_);
lean_dec_ref(v_fst_4844_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4857_, size_t v_i_4858_, size_t v_stop_4859_, lean_object* v_b_4860_){
_start:
{
lean_object* v___y_4862_; uint8_t v___x_4866_; 
v___x_4866_ = lean_usize_dec_eq(v_i_4858_, v_stop_4859_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; lean_object* v_fst_4868_; 
v___x_4867_ = lean_array_uget_borrowed(v_as_4857_, v_i_4858_);
v_fst_4868_ = lean_ctor_get(v___x_4867_, 0);
if (lean_obj_tag(v_fst_4868_) == 0)
{
v___y_4862_ = v_b_4860_;
goto v___jp_4861_;
}
else
{
lean_object* v_val_4869_; lean_object* v___x_4870_; 
v_val_4869_ = lean_ctor_get(v_fst_4868_, 0);
lean_inc(v_val_4869_);
v___x_4870_ = lean_array_push(v_b_4860_, v_val_4869_);
v___y_4862_ = v___x_4870_;
goto v___jp_4861_;
}
}
else
{
return v_b_4860_;
}
v___jp_4861_:
{
size_t v___x_4863_; size_t v___x_4864_; 
v___x_4863_ = ((size_t)1ULL);
v___x_4864_ = lean_usize_add(v_i_4858_, v___x_4863_);
v_i_4858_ = v___x_4864_;
v_b_4860_ = v___y_4862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4871_, lean_object* v_i_4872_, lean_object* v_stop_4873_, lean_object* v_b_4874_){
_start:
{
size_t v_i_boxed_4875_; size_t v_stop_boxed_4876_; lean_object* v_res_4877_; 
v_i_boxed_4875_ = lean_unbox_usize(v_i_4872_);
lean_dec(v_i_4872_);
v_stop_boxed_4876_ = lean_unbox_usize(v_stop_4873_);
lean_dec(v_stop_4873_);
v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4871_, v_i_boxed_4875_, v_stop_boxed_4876_, v_b_4874_);
lean_dec_ref(v_as_4871_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4880_, lean_object* v_start_4881_, lean_object* v_stop_4882_){
_start:
{
lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4883_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4884_ = lean_nat_dec_lt(v_start_4881_, v_stop_4882_);
if (v___x_4884_ == 0)
{
return v___x_4883_;
}
else
{
lean_object* v___x_4885_; uint8_t v___x_4886_; 
v___x_4885_ = lean_array_get_size(v_as_4880_);
v___x_4886_ = lean_nat_dec_le(v_stop_4882_, v___x_4885_);
if (v___x_4886_ == 0)
{
uint8_t v___x_4887_; 
v___x_4887_ = lean_nat_dec_lt(v_start_4881_, v___x_4885_);
if (v___x_4887_ == 0)
{
return v___x_4883_;
}
else
{
size_t v___x_4888_; size_t v___x_4889_; lean_object* v___x_4890_; 
v___x_4888_ = lean_usize_of_nat(v_start_4881_);
v___x_4889_ = lean_usize_of_nat(v___x_4885_);
v___x_4890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4880_, v___x_4888_, v___x_4889_, v___x_4883_);
return v___x_4890_;
}
}
else
{
size_t v___x_4891_; size_t v___x_4892_; lean_object* v___x_4893_; 
v___x_4891_ = lean_usize_of_nat(v_start_4881_);
v___x_4892_ = lean_usize_of_nat(v_stop_4882_);
v___x_4893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4880_, v___x_4891_, v___x_4892_, v___x_4883_);
return v___x_4893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4894_, lean_object* v_start_4895_, lean_object* v_stop_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4894_, v_start_4895_, v_stop_4896_);
lean_dec(v_stop_4896_);
lean_dec(v_start_4895_);
lean_dec_ref(v_as_4894_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4898_, lean_object* v_bs_4899_, lean_object* v_i_4900_, lean_object* v_cs_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4920_ = lean_array_get_size(v_as_4898_);
v___x_4921_ = lean_nat_dec_lt(v_i_4900_, v___x_4920_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec(v_i_4900_);
v___x_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4922_, 0, v_cs_4901_);
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = lean_array_get_size(v_bs_4899_);
v___x_4924_ = lean_nat_dec_lt(v_i_4900_, v___x_4923_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
lean_dec(v_i_4900_);
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v_cs_4901_);
return v___x_4925_;
}
else
{
lean_object* v_a_4926_; lean_object* v_fst_4927_; lean_object* v_snd_4928_; lean_object* v_fst_4930_; lean_object* v_snd_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v_b_4969_; 
v_a_4926_ = lean_array_fget_borrowed(v_as_4898_, v_i_4900_);
v_fst_4927_ = lean_ctor_get(v_a_4926_, 0);
lean_inc(v_fst_4927_);
v_snd_4928_ = lean_ctor_get(v_a_4926_, 1);
v_b_4969_ = lean_array_fget(v_bs_4899_, v_i_4900_);
if (lean_obj_tag(v_b_4969_) == 4)
{
lean_object* v_ref_4970_; lean_object* v_a_4971_; lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5008_; 
v_ref_4970_ = lean_ctor_get(v_b_4969_, 0);
v_a_4971_ = lean_ctor_get(v_b_4969_, 1);
v_a_4972_ = lean_ctor_get(v_b_4969_, 2);
v_isSharedCheck_5008_ = !lean_is_exclusive(v_b_4969_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_4974_ = v_b_4969_;
v_isShared_4975_ = v_isSharedCheck_5008_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_inc(v_a_4971_);
lean_inc(v_ref_4970_);
lean_dec(v_b_4969_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5008_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_toCold_4976_; lean_object* v_currRecDepth_4977_; lean_object* v_ref_4978_; uint16_t v_optionFlags_4979_; uint8_t v_suppressElabErrors_4980_; uint8_t v_isRecordingDeps_4981_; lean_object* v_ref_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v_toCold_4976_ = lean_ctor_get(v___y_4906_, 0);
v_currRecDepth_4977_ = lean_ctor_get(v___y_4906_, 1);
v_ref_4978_ = lean_ctor_get(v___y_4906_, 2);
v_optionFlags_4979_ = lean_ctor_get_uint16(v___y_4906_, sizeof(void*)*3);
v_suppressElabErrors_4980_ = lean_ctor_get_uint8(v___y_4906_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4981_ = lean_ctor_get_uint8(v___y_4906_, sizeof(void*)*3 + 3);
v_ref_4982_ = l_Lean_replaceRef(v_ref_4970_, v_ref_4978_);
lean_inc(v_currRecDepth_4977_);
lean_inc_ref(v_toCold_4976_);
v___x_4983_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4983_, 0, v_toCold_4976_);
lean_ctor_set(v___x_4983_, 1, v_currRecDepth_4977_);
lean_ctor_set(v___x_4983_, 2, v_ref_4982_);
lean_ctor_set_uint16(v___x_4983_, sizeof(void*)*3, v_optionFlags_4979_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*3 + 2, v_suppressElabErrors_4980_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*3 + 3, v_isRecordingDeps_4981_);
v___x_4984_ = l_Lean_Elab_Term_elabType(v_a_4972_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___x_4983_, v___y_4907_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4986_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc_n(v_a_4985_, 2);
lean_dec_ref_known(v___x_4984_, 1);
v___x_4986_ = l_Lean_Elab_Term_exprToSyntax(v_a_4985_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___x_4983_, v___y_4907_);
lean_dec_ref_known(v___x_4983_, 3);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 2, v_a_4987_);
v___x_4989_ = v___x_4974_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_ref_4970_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_a_4971_);
lean_ctor_set(v_reuseFailAlloc_4991_, 2, v_a_4987_);
v___x_4989_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4990_, 0, v_a_4985_);
v_fst_4930_ = v___x_4989_;
v_snd_4931_ = v___x_4990_;
v___y_4932_ = v___y_4902_;
v___y_4933_ = v___y_4903_;
v___y_4934_ = v___y_4904_;
v___y_4935_ = v___y_4905_;
v___y_4936_ = v___y_4906_;
v___y_4937_ = v___y_4907_;
goto v___jp_4929_;
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_a_4985_);
lean_del_object(v___x_4974_);
lean_dec_ref(v_a_4971_);
lean_dec(v_ref_4970_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_cs_4901_);
lean_dec(v_i_4900_);
v_a_4992_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4986_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4986_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref_known(v___x_4983_, 3);
lean_del_object(v___x_4974_);
lean_dec_ref(v_a_4971_);
lean_dec(v_ref_4970_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_cs_4901_);
lean_dec(v_i_4900_);
v_a_5000_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4984_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4984_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
}
else
{
lean_object* v___x_5009_; 
v___x_5009_ = lean_box(0);
v_fst_4930_ = v_b_4969_;
v_snd_4931_ = v___x_5009_;
v___y_4932_ = v___y_4902_;
v___y_4933_ = v___y_4903_;
v___y_4934_ = v___y_4904_;
v___y_4935_ = v___y_4905_;
v___y_4936_ = v___y_4906_;
v___y_4937_ = v___y_4907_;
goto v___jp_4929_;
}
v___jp_4929_:
{
lean_object* v___x_4938_; 
lean_inc(v_snd_4931_);
lean_inc(v_snd_4928_);
v___x_4938_ = l_Lean_Elab_Term_elabTerm(v_snd_4928_, v_snd_4931_, v___x_4924_, v___x_4924_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v___x_4940_ = lean_box(0);
v___x_4941_ = l_Lean_Elab_Term_ensureHasType(v_snd_4931_, v_a_4939_, v___x_4940_, v___x_4940_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; lean_object* v___x_4943_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
lean_inc(v_a_4942_);
lean_dec_ref_known(v___x_4941_, 1);
v___x_4943_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4930_);
if (lean_obj_tag(v_fst_4927_) == 0)
{
v___y_4910_ = v_a_4942_;
v___y_4911_ = v_fst_4930_;
v___y_4912_ = v___x_4943_;
v___y_4913_ = v___x_4940_;
goto v___jp_4909_;
}
else
{
lean_object* v_val_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4952_; 
v_val_4944_ = lean_ctor_get(v_fst_4927_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_fst_4927_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4946_ = v_fst_4927_;
v_isShared_4947_ = v_isSharedCheck_4952_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_val_4944_);
lean_dec(v_fst_4927_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4952_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4948_; lean_object* v___x_4950_; 
v___x_4948_ = l_Lean_TSyntax_getId(v_val_4944_);
lean_dec(v_val_4944_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v___x_4948_);
v___x_4950_ = v___x_4946_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
v___y_4910_ = v_a_4942_;
v___y_4911_ = v_fst_4930_;
v___y_4912_ = v___x_4943_;
v___y_4913_ = v___x_4950_;
goto v___jp_4909_;
}
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_dec_ref(v_fst_4930_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_cs_4901_);
lean_dec(v_i_4900_);
v_a_4953_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4941_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4941_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec(v_snd_4931_);
lean_dec_ref(v_fst_4930_);
lean_dec(v_fst_4927_);
lean_dec_ref(v_cs_4901_);
lean_dec(v_i_4900_);
v_a_4961_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4938_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4938_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
}
v___jp_4909_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4914_, 0, v___y_4910_);
lean_ctor_set(v___x_4914_, 1, v___y_4912_);
lean_ctor_set(v___x_4914_, 2, v___y_4913_);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___y_4911_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
v___x_4916_ = lean_unsigned_to_nat(1u);
v___x_4917_ = lean_nat_add(v_i_4900_, v___x_4916_);
lean_dec(v_i_4900_);
v___x_4918_ = lean_array_push(v_cs_4901_, v___x_4915_);
v_i_4900_ = v___x_4917_;
v_cs_4901_ = v___x_4918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_5010_, lean_object* v_bs_5011_, lean_object* v_i_5012_, lean_object* v_cs_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_5010_, v_bs_5011_, v_i_5012_, v_cs_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec_ref(v_bs_5011_);
lean_dec_ref(v_as_5010_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5024_, lean_object* v_g_5025_, lean_object* v_pats_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5034_ = lean_array_mk(v_pats_5026_);
v___x_5035_ = lean_unsigned_to_nat(0u);
v___x_5036_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5037_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5024_, v___x_5034_, v___x_5035_, v___x_5036_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec_ref(v___x_5034_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5039_; lean_object* v_fst_5040_; lean_object* v_snd_5041_; lean_object* v___x_5042_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_a_5038_);
lean_dec_ref_known(v___x_5037_, 1);
v___x_5039_ = l_Array_unzip___redArg(v_a_5038_);
lean_dec(v_a_5038_);
v_fst_5040_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_fst_5040_);
v_snd_5041_ = lean_ctor_get(v___x_5039_, 1);
lean_inc(v_snd_5041_);
lean_dec_ref(v___x_5039_);
v___x_5042_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5025_, v_snd_5041_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v_snd_5041_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v_snd_5044_; lean_object* v_fst_5045_; lean_object* v_fst_5046_; lean_object* v_snd_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v_snd_5044_ = lean_ctor_get(v_a_5043_, 1);
lean_inc(v_snd_5044_);
v_fst_5045_ = lean_ctor_get(v_a_5043_, 0);
lean_inc(v_fst_5045_);
lean_dec(v_a_5043_);
v_fst_5046_ = lean_ctor_get(v_snd_5044_, 0);
lean_inc(v_fst_5046_);
v_snd_5047_ = lean_ctor_get(v_snd_5044_, 1);
lean_inc(v_snd_5047_);
lean_dec(v_snd_5044_);
v___x_5048_ = lean_array_get_size(v_tgts_5024_);
v___x_5049_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5024_, v___x_5035_, v___x_5048_);
v___x_5050_ = l_Array_zip___redArg(v___x_5049_, v_fst_5046_);
lean_dec(v_fst_5046_);
lean_dec_ref(v___x_5049_);
v___x_5051_ = lean_box(0);
v___x_5052_ = l_Array_zip___redArg(v_fst_5040_, v_fst_5045_);
lean_dec(v_fst_5045_);
lean_dec(v_fst_5040_);
v___x_5053_ = lean_array_to_list(v___x_5052_);
v___x_5054_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5054_, 0, v___x_5050_);
v___x_5055_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5047_, v___x_5051_, v___x_5036_, v___x_5036_, v___x_5053_, v___x_5054_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5064_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5058_ = v___x_5055_;
v_isShared_5059_ = v_isSharedCheck_5064_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5055_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5064_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5060_ = lean_array_to_list(v_a_5056_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5060_);
v___x_5062_ = v___x_5058_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
v_a_5065_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5055_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5055_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_fst_5040_);
v_a_5073_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5042_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5042_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec(v_g_5025_);
v_a_5081_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5037_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5037_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5089_, lean_object* v_g_5090_, lean_object* v_pats_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5089_, v_g_5090_, v_pats_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec_ref(v_tgts_5089_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5100_, size_t v_sz_5101_, size_t v_i_5102_, lean_object* v_bs_5103_){
_start:
{
uint8_t v___x_5104_; 
v___x_5104_ = lean_usize_dec_lt(v_i_5102_, v_sz_5101_);
if (v___x_5104_ == 0)
{
return v_bs_5103_;
}
else
{
lean_object* v___x_5105_; uint8_t v___x_5106_; lean_object* v___x_5107_; lean_object* v_bs_x27_5108_; uint8_t v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; size_t v___x_5112_; size_t v___x_5113_; lean_object* v___x_5114_; 
v___x_5105_ = lean_unsigned_to_nat(1u);
v___x_5106_ = lean_nat_dec_eq(v___x_5100_, v___x_5105_);
v___x_5107_ = lean_unsigned_to_nat(0u);
v_bs_x27_5108_ = lean_array_uset(v_bs_5103_, v_i_5102_, v___x_5107_);
v___x_5109_ = 0;
v___x_5110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_5111_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5111_, 0, v___x_5110_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1, v___x_5109_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 1, v___x_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 2, v___x_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 3, v___x_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 4, v___x_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 5, v___x_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*1 + 6, v___x_5106_);
v___x_5112_ = ((size_t)1ULL);
v___x_5113_ = lean_usize_add(v_i_5102_, v___x_5112_);
v___x_5114_ = lean_array_uset(v_bs_x27_5108_, v_i_5102_, v___x_5111_);
v_i_5102_ = v___x_5113_;
v_bs_5103_ = v___x_5114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5116_, lean_object* v_sz_5117_, lean_object* v_i_5118_, lean_object* v_bs_5119_){
_start:
{
size_t v_sz_boxed_5120_; size_t v_i_boxed_5121_; lean_object* v_res_5122_; 
v_sz_boxed_5120_ = lean_unbox_usize(v_sz_5117_);
lean_dec(v_sz_5117_);
v_i_boxed_5121_ = lean_unbox_usize(v_i_5118_);
lean_dec(v_i_5118_);
v_res_5122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5116_, v_sz_boxed_5120_, v_i_boxed_5121_, v_bs_5119_);
lean_dec(v___x_5116_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5123_, lean_object* v___x_5124_, lean_object* v_pat_5125_, lean_object* v_tgts_5126_, lean_object* v___x_5127_, lean_object* v___f_5128_, lean_object* v_g_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
if (v___x_5123_ == 0)
{
lean_object* v___x_5137_; uint8_t v___x_5138_; lean_object* v___y_5140_; 
lean_dec(v_g_5129_);
v___x_5137_ = lean_unsigned_to_nat(1u);
v___x_5138_ = lean_nat_dec_eq(v___x_5124_, v___x_5137_);
if (v___x_5138_ == 0)
{
lean_object* v_ref_5149_; 
v_ref_5149_ = lean_ctor_get(v_pat_5125_, 0);
lean_inc(v_ref_5149_);
v___y_5140_ = v_ref_5149_;
goto v___jp_5139_;
}
else
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec_ref(v_tgts_5126_);
v___x_5150_ = lean_box(0);
v___x_5151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5151_, 0, v_pat_5125_);
lean_ctor_set(v___x_5151_, 1, v___x_5150_);
lean_inc(v___y_5135_);
lean_inc_ref(v___y_5134_);
lean_inc(v___y_5133_);
lean_inc_ref(v___y_5132_);
lean_inc(v___y_5131_);
lean_inc_ref(v___y_5130_);
v___x_5152_ = lean_apply_8(v___f_5128_, v___x_5151_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, lean_box(0));
return v___x_5152_;
}
v___jp_5139_:
{
lean_object* v___x_5141_; lean_object* v_snd_5142_; size_t v_sz_5143_; size_t v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v_snd_5147_; lean_object* v___x_5148_; 
v___x_5141_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5125_);
v_snd_5142_ = lean_ctor_get(v___x_5141_, 1);
lean_inc(v_snd_5142_);
lean_dec_ref(v___x_5141_);
v_sz_5143_ = lean_array_size(v_tgts_5126_);
v___x_5144_ = ((size_t)0ULL);
v___x_5145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5124_, v_sz_5143_, v___x_5144_, v_tgts_5126_);
v___x_5146_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5140_, v___x_5145_, v___x_5138_, v___x_5127_, v_snd_5142_);
lean_dec_ref(v___x_5145_);
v_snd_5147_ = lean_ctor_get(v___x_5146_, 1);
lean_inc(v_snd_5147_);
lean_dec_ref(v___x_5146_);
lean_inc(v___y_5135_);
lean_inc_ref(v___y_5134_);
lean_inc(v___y_5133_);
lean_inc_ref(v___y_5132_);
lean_inc(v___y_5131_);
lean_inc_ref(v___y_5130_);
v___x_5148_ = lean_apply_8(v___f_5128_, v_snd_5147_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, lean_box(0));
return v___x_5148_;
}
}
else
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
lean_dec_ref(v___f_5128_);
lean_dec_ref(v_tgts_5126_);
lean_dec_ref(v_pat_5125_);
v___x_5153_ = lean_box(0);
v___x_5154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_g_5129_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
v___x_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
return v___x_5155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5156_, lean_object* v___x_5157_, lean_object* v_pat_5158_, lean_object* v_tgts_5159_, lean_object* v___x_5160_, lean_object* v___f_5161_, lean_object* v_g_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
uint8_t v___x_5079__boxed_5170_; lean_object* v_res_5171_; 
v___x_5079__boxed_5170_ = lean_unbox(v___x_5156_);
v_res_5171_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5079__boxed_5170_, v___x_5157_, v_pat_5158_, v_tgts_5159_, v___x_5160_, v___f_5161_, v_g_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___x_5160_);
lean_dec(v___x_5157_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5172_, lean_object* v_pat_5173_, lean_object* v_g_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v___f_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; uint8_t v___x_5185_; lean_object* v___x_5186_; lean_object* v___y_5187_; uint8_t v___x_5188_; lean_object* v___x_5189_; 
lean_inc(v_g_5174_);
lean_inc_ref(v_tgts_5172_);
v___f_5182_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5182_, 0, v_tgts_5172_);
lean_closure_set(v___f_5182_, 1, v_g_5174_);
v___x_5183_ = lean_array_get_size(v_tgts_5172_);
v___x_5184_ = lean_unsigned_to_nat(0u);
v___x_5185_ = lean_nat_dec_eq(v___x_5183_, v___x_5184_);
v___x_5186_ = lean_box(v___x_5185_);
v___y_5187_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5187_, 0, v___x_5186_);
lean_closure_set(v___y_5187_, 1, v___x_5183_);
lean_closure_set(v___y_5187_, 2, v_pat_5173_);
lean_closure_set(v___y_5187_, 3, v_tgts_5172_);
lean_closure_set(v___y_5187_, 4, v___x_5184_);
lean_closure_set(v___y_5187_, 5, v___f_5182_);
lean_closure_set(v___y_5187_, 6, v_g_5174_);
v___x_5188_ = 1;
v___x_5189_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5187_, v___x_5188_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5190_, lean_object* v_pat_5191_, lean_object* v_g_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5190_, v_pat_5191_, v_g_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_);
lean_dec(v_a_5198_);
lean_dec_ref(v_a_5197_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5205_, lean_object* v_g_5206_, lean_object* v_pat_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = l_Lean_Elab_Term_elabType(v_ty_5205_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
lean_inc_n(v_a_5216_, 2);
lean_dec_ref_known(v___x_5215_, 1);
v___x_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5217_, 0, v_a_5216_);
v___x_5218_ = 0;
v___x_5219_ = lean_box(0);
v___x_5220_ = l_Lean_Meta_mkFreshExprMVar(v___x_5217_, v___x_5218_, v___x_5219_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; lean_object* v___y_5223_; lean_object* v___x_5277_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref_known(v___x_5220_, 1);
v___x_5277_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5207_);
if (lean_obj_tag(v___x_5277_) == 0)
{
v___y_5223_ = v___x_5219_;
goto v___jp_5222_;
}
else
{
lean_object* v_val_5278_; 
v_val_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc(v_val_5278_);
lean_dec_ref_known(v___x_5277_, 1);
v___y_5223_ = v_val_5278_;
goto v___jp_5222_;
}
v___jp_5222_:
{
lean_object* v___x_5224_; 
lean_inc(v_a_5221_);
v___x_5224_ = l_Lean_MVarId_assert(v_g_5206_, v___y_5223_, v_a_5216_, v_a_5221_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; uint8_t v___x_5226_; lean_object* v___x_5227_; 
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5225_);
lean_dec_ref_known(v___x_5224_, 1);
v___x_5226_ = 0;
v___x_5227_ = l_Lean_Meta_intro1Core(v_a_5225_, v___x_5226_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v_fst_5229_; lean_object* v_snd_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5260_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
v_fst_5229_ = lean_ctor_get(v_a_5228_, 0);
v_snd_5230_ = lean_ctor_get(v_a_5228_, 1);
v_isSharedCheck_5260_ = !lean_is_exclusive(v_a_5228_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5232_ = v_a_5228_;
v_isShared_5233_ = v_isSharedCheck_5260_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_snd_5230_);
lean_inc(v_fst_5229_);
lean_dec(v_a_5228_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5260_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5234_ = lean_box(0);
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5236_ = l_Lean_Expr_fvar___override(v_fst_5229_);
v___x_5237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5238_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5230_, v___x_5234_, v___x_5235_, v___x_5236_, v___x_5235_, v_pat_5207_, v___x_5237_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
lean_dec_ref(v___x_5236_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5251_; 
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5241_ = v___x_5238_;
v_isShared_5242_ = v_isSharedCheck_5251_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5238_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5251_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5246_; 
v___x_5243_ = l_Lean_Expr_mvarId_x21(v_a_5221_);
lean_dec(v_a_5221_);
v___x_5244_ = lean_array_to_list(v_a_5239_);
if (v_isShared_5233_ == 0)
{
lean_ctor_set_tag(v___x_5232_, 1);
lean_ctor_set(v___x_5232_, 1, v___x_5244_);
lean_ctor_set(v___x_5232_, 0, v___x_5243_);
v___x_5246_ = v___x_5232_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5250_, 1, v___x_5244_);
v___x_5246_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
lean_object* v___x_5248_; 
if (v_isShared_5242_ == 0)
{
lean_ctor_set(v___x_5241_, 0, v___x_5246_);
v___x_5248_ = v___x_5241_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
else
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
lean_del_object(v___x_5232_);
lean_dec(v_a_5221_);
v_a_5252_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5238_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5238_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_pat_5207_);
v_a_5261_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5227_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5227_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_pat_5207_);
v_a_5269_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5224_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5224_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5286_; 
lean_dec(v_a_5216_);
lean_dec_ref(v_pat_5207_);
lean_dec(v_g_5206_);
v_a_5279_ = lean_ctor_get(v___x_5220_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5281_ = v___x_5220_;
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5220_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5284_; 
if (v_isShared_5282_ == 0)
{
v___x_5284_ = v___x_5281_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_dec_ref(v_pat_5207_);
lean_dec(v_g_5206_);
v_a_5287_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5215_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5215_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5295_, lean_object* v_g_5296_, lean_object* v_pat_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5295_, v_g_5296_, v_pat_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5306_, lean_object* v_ty_5307_, lean_object* v_g_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_){
_start:
{
lean_object* v___f_5316_; uint8_t v___x_5317_; lean_object* v___x_5318_; 
v___f_5316_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5316_, 0, v_ty_5307_);
lean_closure_set(v___f_5316_, 1, v_g_5308_);
lean_closure_set(v___f_5316_, 2, v_pat_5306_);
v___x_5317_ = 1;
v___x_5318_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5316_, v___x_5317_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5319_, lean_object* v_ty_5320_, lean_object* v_g_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5319_, v_ty_5320_, v_g_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
lean_dec(v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5337_, lean_object* v_acc_5338_, lean_object* v_ty_x3f_5339_){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; uint8_t v___x_5342_; 
v___x_5340_ = lean_unsigned_to_nat(0u);
v___x_5341_ = lean_array_get_size(v_pats_5337_);
v___x_5342_ = lean_nat_dec_lt(v___x_5340_, v___x_5341_);
if (v___x_5342_ == 0)
{
lean_dec(v_ty_x3f_5339_);
return v_acc_5338_;
}
else
{
uint8_t v___x_5343_; 
v___x_5343_ = lean_nat_dec_le(v___x_5341_, v___x_5341_);
if (v___x_5343_ == 0)
{
if (v___x_5342_ == 0)
{
lean_dec(v_ty_x3f_5339_);
return v_acc_5338_;
}
else
{
size_t v___x_5344_; size_t v___x_5345_; lean_object* v___x_5346_; 
v___x_5344_ = ((size_t)0ULL);
v___x_5345_ = lean_usize_of_nat(v___x_5341_);
v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5339_, v_pats_5337_, v___x_5344_, v___x_5345_, v_acc_5338_);
return v___x_5346_;
}
}
else
{
size_t v___x_5347_; size_t v___x_5348_; lean_object* v___x_5349_; 
v___x_5347_ = ((size_t)0ULL);
v___x_5348_ = lean_usize_of_nat(v___x_5341_);
v___x_5349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5339_, v_pats_5337_, v___x_5347_, v___x_5348_, v_acc_5338_);
return v___x_5349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5353_, lean_object* v_acc_5354_, lean_object* v_ty_x3f_5355_){
_start:
{
lean_object* v___x_5356_; uint8_t v___x_5357_; 
v___x_5356_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5353_);
v___x_5357_ = l_Lean_Syntax_isOfKind(v_pat_5353_, v___x_5356_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; uint8_t v___x_5359_; 
v___x_5358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5353_);
v___x_5359_ = l_Lean_Syntax_isOfKind(v_pat_5353_, v___x_5358_);
if (v___x_5359_ == 0)
{
lean_dec(v_ty_x3f_5355_);
lean_dec(v_pat_5353_);
return v_acc_5354_;
}
else
{
lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; uint8_t v___x_5364_; 
v___x_5360_ = lean_unsigned_to_nat(1u);
v___x_5361_ = l_Lean_Syntax_getArg(v_pat_5353_, v___x_5360_);
v___x_5362_ = lean_unsigned_to_nat(2u);
v___x_5363_ = l_Lean_Syntax_getArg(v_pat_5353_, v___x_5362_);
lean_dec(v_pat_5353_);
v___x_5364_ = l_Lean_Syntax_isNone(v___x_5363_);
if (v___x_5364_ == 0)
{
uint8_t v___x_5365_; 
lean_dec(v_ty_x3f_5355_);
lean_inc(v___x_5363_);
v___x_5365_ = l_Lean_Syntax_matchesNull(v___x_5363_, v___x_5362_);
if (v___x_5365_ == 0)
{
lean_dec(v___x_5363_);
lean_dec(v___x_5361_);
return v_acc_5354_;
}
else
{
lean_object* v_ty_x3f_x27_5366_; lean_object* v___x_5367_; lean_object* v_pats_5368_; lean_object* v___x_5369_; 
v_ty_x3f_x27_5366_ = l_Lean_Syntax_getArg(v___x_5363_, v___x_5360_);
lean_dec(v___x_5363_);
v___x_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5367_, 0, v_ty_x3f_x27_5366_);
v_pats_5368_ = l_Lean_Syntax_getArgs(v___x_5361_);
lean_dec(v___x_5361_);
v___x_5369_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5368_, v_acc_5354_, v___x_5367_);
lean_dec_ref(v_pats_5368_);
return v___x_5369_;
}
}
else
{
lean_object* v_pats_5370_; lean_object* v___x_5371_; 
lean_dec(v___x_5363_);
v_pats_5370_ = l_Lean_Syntax_getArgs(v___x_5361_);
lean_dec(v___x_5361_);
v___x_5371_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5370_, v_acc_5354_, v_ty_x3f_5355_);
lean_dec_ref(v_pats_5370_);
return v___x_5371_;
}
}
}
else
{
lean_object* v___x_5372_; lean_object* v_p_5373_; 
v___x_5372_ = lean_unsigned_to_nat(0u);
v_p_5373_ = l_Lean_Syntax_getArg(v_pat_5353_, v___x_5372_);
lean_dec(v_pat_5353_);
if (lean_obj_tag(v_ty_x3f_5355_) == 0)
{
lean_object* v___x_5374_; 
v___x_5374_ = lean_array_push(v_acc_5354_, v_p_5373_);
return v___x_5374_;
}
else
{
lean_object* v_val_5375_; lean_object* v___x_5376_; lean_object* v_ref_5377_; uint8_t v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v_val_5375_ = lean_ctor_get(v_ty_x3f_5355_, 0);
lean_inc(v_val_5375_);
lean_dec_ref_known(v_ty_x3f_5355_, 1);
v___x_5376_ = lean_box(0);
v_ref_5377_ = l_Lean_replaceRef(v_p_5373_, v___x_5376_);
v___x_5378_ = 0;
v___x_5379_ = l_Lean_SourceInfo_fromRef(v_ref_5377_, v___x_5378_);
lean_dec(v_ref_5377_);
v___x_5380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5379_, 7);
v___x_5382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5382_, 0, v___x_5379_);
lean_ctor_set(v___x_5382_, 1, v___x_5381_);
v___x_5383_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5384_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5385_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5386_ = l_Lean_Syntax_node1(v___x_5379_, v___x_5385_, v_p_5373_);
v___x_5387_ = l_Lean_Syntax_node1(v___x_5379_, v___x_5384_, v___x_5386_);
v___x_5388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5379_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_Syntax_node2(v___x_5379_, v___x_5385_, v___x_5389_, v_val_5375_);
v___x_5391_ = l_Lean_Syntax_node2(v___x_5379_, v___x_5383_, v___x_5387_, v___x_5390_);
v___x_5392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5379_);
lean_ctor_set(v___x_5393_, 1, v___x_5392_);
v___x_5394_ = l_Lean_Syntax_node3(v___x_5379_, v___x_5380_, v___x_5382_, v___x_5391_, v___x_5393_);
v___x_5395_ = lean_array_push(v_acc_5354_, v___x_5394_);
return v___x_5395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5396_, lean_object* v_as_5397_, size_t v_i_5398_, size_t v_stop_5399_, lean_object* v_b_5400_){
_start:
{
uint8_t v___x_5401_; 
v___x_5401_ = lean_usize_dec_eq(v_i_5398_, v_stop_5399_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; lean_object* v___x_5403_; size_t v___x_5404_; size_t v___x_5405_; 
v___x_5402_ = lean_array_uget_borrowed(v_as_5397_, v_i_5398_);
lean_inc(v_ty_x3f_5396_);
lean_inc(v___x_5402_);
v___x_5403_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5402_, v_b_5400_, v_ty_x3f_5396_);
v___x_5404_ = ((size_t)1ULL);
v___x_5405_ = lean_usize_add(v_i_5398_, v___x_5404_);
v_i_5398_ = v___x_5405_;
v_b_5400_ = v___x_5403_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5396_);
return v_b_5400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5407_, lean_object* v_as_5408_, lean_object* v_i_5409_, lean_object* v_stop_5410_, lean_object* v_b_5411_){
_start:
{
size_t v_i_boxed_5412_; size_t v_stop_boxed_5413_; lean_object* v_res_5414_; 
v_i_boxed_5412_ = lean_unbox_usize(v_i_5409_);
lean_dec(v_i_5409_);
v_stop_boxed_5413_ = lean_unbox_usize(v_stop_5410_);
lean_dec(v_stop_5410_);
v_res_5414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5407_, v_as_5408_, v_i_boxed_5412_, v_stop_boxed_5413_, v_b_5411_);
lean_dec_ref(v_as_5408_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5415_, lean_object* v_acc_5416_, lean_object* v_ty_x3f_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5415_, v_acc_5416_, v_ty_x3f_5417_);
lean_dec_ref(v_pats_5415_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5420_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5421_, 0, v___x_5420_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5424_, lean_object* v_pats_5425_, lean_object* v_ty_x3f_5426_, lean_object* v_cont_5427_, lean_object* v_i_5428_, lean_object* v_g_5429_, lean_object* v_fs_5430_, lean_object* v_clears_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5424_, v_pats_5425_, v_ty_x3f_5426_, v_cont_5427_, v_i_5428_, v_g_5429_, v_fs_5430_, v_clears_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_i_5428_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5441_ = _args[0];
lean_object* v_ref_5442_ = _args[1];
lean_object* v_pats_5443_ = _args[2];
lean_object* v_ty_x3f_5444_ = _args[3];
lean_object* v_cont_5445_ = _args[4];
lean_object* v_i_5446_ = _args[5];
lean_object* v_g_5447_ = _args[6];
lean_object* v_fs_5448_ = _args[7];
lean_object* v_clears_5449_ = _args[8];
lean_object* v_a_5450_ = _args[9];
lean_object* v_a_5451_ = _args[10];
lean_object* v_a_5452_ = _args[11];
lean_object* v_a_5453_ = _args[12];
lean_object* v_a_5454_ = _args[13];
lean_object* v_a_5455_ = _args[14];
lean_object* v_a_5456_ = _args[15];
lean_object* v_a_5457_ = _args[16];
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5441_, v_ref_5442_, v_pats_5443_, v_ty_x3f_5444_, v_cont_5445_, v_i_5446_, v_g_5447_, v_fs_5448_, v_clears_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_);
lean_dec(v_a_5456_);
lean_dec_ref(v_a_5455_);
lean_dec(v_a_5454_);
lean_dec_ref(v_a_5453_);
lean_dec(v_a_5452_);
lean_dec_ref(v_a_5451_);
lean_dec(v_i_5446_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5459_, lean_object* v_fs_5460_, lean_object* v_clears_5461_, lean_object* v_ref_5462_, lean_object* v_pats_5463_, lean_object* v_ty_x3f_5464_, lean_object* v_a_5465_, lean_object* v_cont_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_){
_start:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5474_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5459_);
v___x_5475_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5475_, 0, lean_box(0));
lean_closure_set(v___x_5475_, 1, v_ref_5462_);
lean_closure_set(v___x_5475_, 2, v_pats_5463_);
lean_closure_set(v___x_5475_, 3, v_ty_x3f_5464_);
lean_closure_set(v___x_5475_, 4, v_cont_5466_);
lean_closure_set(v___x_5475_, 5, v___x_5474_);
lean_closure_set(v___x_5475_, 6, v_g_5459_);
lean_closure_set(v___x_5475_, 7, v_fs_5460_);
lean_closure_set(v___x_5475_, 8, v_clears_5461_);
lean_closure_set(v___x_5475_, 9, v_a_5465_);
v___x_5476_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5459_, v___x_5475_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5477_, lean_object* v_fs_5478_, lean_object* v_clears_5479_, lean_object* v_a_5480_, lean_object* v_ref_5481_, lean_object* v_pat_5482_, lean_object* v_ty_x3f_5483_, lean_object* v_cont_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_){
_start:
{
lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___x_5504_; uint8_t v___x_5505_; 
v___x_5504_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5482_);
v___x_5505_ = l_Lean_Syntax_isOfKind(v_pat_5482_, v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; uint8_t v___x_5507_; 
lean_dec(v_ref_5481_);
v___x_5506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5482_);
v___x_5507_ = l_Lean_Syntax_isOfKind(v_pat_5482_, v___x_5506_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; 
lean_dec_ref(v_cont_5484_);
lean_dec(v_ty_x3f_5483_);
lean_dec(v_pat_5482_);
lean_dec(v_a_5480_);
lean_dec_ref(v_clears_5479_);
lean_dec(v_fs_5478_);
lean_dec(v_g_5477_);
v___x_5508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5508_;
}
else
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v_ty_x3f_x27_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___y_5517_; lean_object* v___y_5518_; lean_object* v___x_5523_; lean_object* v___x_5524_; uint8_t v___x_5525_; 
v___x_5509_ = lean_unsigned_to_nat(1u);
v___x_5510_ = l_Lean_Syntax_getArg(v_pat_5482_, v___x_5509_);
v___x_5523_ = lean_unsigned_to_nat(2u);
v___x_5524_ = l_Lean_Syntax_getArg(v_pat_5482_, v___x_5523_);
v___x_5525_ = l_Lean_Syntax_isNone(v___x_5524_);
if (v___x_5525_ == 0)
{
uint8_t v___x_5526_; 
lean_inc(v___x_5524_);
v___x_5526_ = l_Lean_Syntax_matchesNull(v___x_5524_, v___x_5523_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; 
lean_dec(v___x_5524_);
lean_dec(v___x_5510_);
lean_dec_ref(v_cont_5484_);
lean_dec(v_ty_x3f_5483_);
lean_dec(v_pat_5482_);
lean_dec(v_a_5480_);
lean_dec_ref(v_clears_5479_);
lean_dec(v_fs_5478_);
lean_dec(v_g_5477_);
v___x_5527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5527_;
}
else
{
lean_object* v_ty_x3f_x27_5528_; lean_object* v___x_5529_; 
v_ty_x3f_x27_5528_ = l_Lean_Syntax_getArg(v___x_5524_, v___x_5509_);
lean_dec(v___x_5524_);
v___x_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5529_, 0, v_ty_x3f_x27_5528_);
v_ty_x3f_x27_5512_ = v___x_5529_;
v___y_5513_ = v_a_5485_;
v___y_5514_ = v_a_5486_;
v___y_5515_ = v_a_5487_;
v___y_5516_ = v_a_5488_;
v___y_5517_ = v_a_5489_;
v___y_5518_ = v_a_5490_;
goto v___jp_5511_;
}
}
else
{
lean_object* v___x_5530_; 
lean_dec(v___x_5524_);
v___x_5530_ = lean_box(0);
v_ty_x3f_x27_5512_ = v___x_5530_;
v___y_5513_ = v_a_5485_;
v___y_5514_ = v_a_5486_;
v___y_5515_ = v_a_5487_;
v___y_5516_ = v_a_5488_;
v___y_5517_ = v_a_5489_;
v___y_5518_ = v_a_5490_;
goto v___jp_5511_;
}
v___jp_5511_:
{
lean_object* v_pats_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; 
v_pats_5519_ = l_Lean_Syntax_getArgs(v___x_5510_);
lean_dec(v___x_5510_);
v___x_5520_ = lean_array_get_size(v_pats_5519_);
v___x_5521_ = lean_nat_dec_eq(v___x_5520_, v___x_5509_);
if (v___x_5521_ == 0)
{
lean_object* v___x_5522_; 
lean_dec(v_pat_5482_);
v___x_5522_ = lean_box(0);
v___y_5493_ = v___y_5516_;
v___y_5494_ = v___y_5517_;
v___y_5495_ = v___y_5518_;
v___y_5496_ = v___y_5514_;
v___y_5497_ = v___y_5515_;
v___y_5498_ = v_ty_x3f_x27_5512_;
v___y_5499_ = v_pats_5519_;
v___y_5500_ = v___y_5513_;
v___y_5501_ = v___x_5522_;
goto v___jp_5492_;
}
else
{
v___y_5493_ = v___y_5516_;
v___y_5494_ = v___y_5517_;
v___y_5495_ = v___y_5518_;
v___y_5496_ = v___y_5514_;
v___y_5497_ = v___y_5515_;
v___y_5498_ = v_ty_x3f_x27_5512_;
v___y_5499_ = v_pats_5519_;
v___y_5500_ = v___y_5513_;
v___y_5501_ = v_pat_5482_;
goto v___jp_5492_;
}
}
}
}
else
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5531_ = lean_unsigned_to_nat(0u);
v___x_5532_ = l_Lean_Syntax_getArg(v_pat_5482_, v___x_5531_);
lean_dec(v_pat_5482_);
v___x_5533_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5532_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5562_; lean_object* v_ref_5566_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
v___x_5535_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5481_, v_a_5534_, v_ty_x3f_5483_);
lean_dec(v_ty_x3f_5483_);
v_ref_5566_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_ref_5566_);
v___y_5562_ = v_ref_5566_;
goto v___jp_5561_;
v___jp_5536_:
{
lean_object* v_toCold_5539_; lean_object* v_currRecDepth_5540_; lean_object* v_ref_5541_; uint16_t v_optionFlags_5542_; uint8_t v_suppressElabErrors_5543_; uint8_t v_isRecordingDeps_5544_; lean_object* v_ref_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v_toCold_5539_ = lean_ctor_get(v_a_5489_, 0);
v_currRecDepth_5540_ = lean_ctor_get(v_a_5489_, 1);
v_ref_5541_ = lean_ctor_get(v_a_5489_, 2);
v_optionFlags_5542_ = lean_ctor_get_uint16(v_a_5489_, sizeof(void*)*3);
v_suppressElabErrors_5543_ = lean_ctor_get_uint8(v_a_5489_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5544_ = lean_ctor_get_uint8(v_a_5489_, sizeof(void*)*3 + 3);
v_ref_5545_ = l_Lean_replaceRef(v___y_5537_, v_ref_5541_);
lean_dec(v___y_5537_);
lean_inc(v_currRecDepth_5540_);
lean_inc_ref(v_toCold_5539_);
v___x_5546_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5546_, 0, v_toCold_5539_);
lean_ctor_set(v___x_5546_, 1, v_currRecDepth_5540_);
lean_ctor_set(v___x_5546_, 2, v_ref_5545_);
lean_ctor_set_uint16(v___x_5546_, sizeof(void*)*3, v_optionFlags_5542_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*3 + 2, v_suppressElabErrors_5543_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*3 + 3, v_isRecordingDeps_5544_);
v___x_5547_ = l_Lean_MVarId_intro(v_g_5477_, v___y_5538_, v_a_5487_, v_a_5488_, v___x_5546_, v_a_5490_);
lean_dec_ref_known(v___x_5546_, 3);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; lean_object* v_fst_5549_; lean_object* v_snd_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_a_5548_);
lean_dec_ref_known(v___x_5547_, 1);
v_fst_5549_ = lean_ctor_get(v_a_5548_, 0);
lean_inc(v_fst_5549_);
v_snd_5550_ = lean_ctor_get(v_a_5548_, 1);
lean_inc(v_snd_5550_);
lean_dec(v_a_5548_);
v___x_5551_ = l_Lean_Expr_fvar___override(v_fst_5549_);
v___x_5552_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5550_, v_fs_5478_, v_clears_5479_, v___x_5551_, v_a_5480_, v___x_5535_, v_cont_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_);
lean_dec_ref(v___x_5551_);
return v___x_5552_;
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5560_; 
lean_dec_ref(v___x_5535_);
lean_dec_ref(v_cont_5484_);
lean_dec(v_a_5480_);
lean_dec_ref(v_clears_5479_);
lean_dec(v_fs_5478_);
v_a_5553_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5555_ = v___x_5547_;
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5547_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5558_; 
if (v_isShared_5556_ == 0)
{
v___x_5558_ = v___x_5555_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5553_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
}
v___jp_5561_:
{
lean_object* v___x_5563_; 
v___x_5563_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5535_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v___x_5564_; 
v___x_5564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5537_ = v___y_5562_;
v___y_5538_ = v___x_5564_;
goto v___jp_5536_;
}
else
{
lean_object* v_val_5565_; 
v_val_5565_ = lean_ctor_get(v___x_5563_, 0);
lean_inc(v_val_5565_);
lean_dec_ref_known(v___x_5563_, 1);
v___y_5537_ = v___y_5562_;
v___y_5538_ = v_val_5565_;
goto v___jp_5536_;
}
}
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec_ref(v_cont_5484_);
lean_dec(v_ty_x3f_5483_);
lean_dec(v_ref_5481_);
lean_dec(v_a_5480_);
lean_dec_ref(v_clears_5479_);
lean_dec(v_fs_5478_);
lean_dec(v_g_5477_);
v_a_5567_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5533_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5533_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
v___jp_5492_:
{
if (lean_obj_tag(v___y_5498_) == 0)
{
lean_object* v___x_5502_; 
v___x_5502_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5477_, v_fs_5478_, v_clears_5479_, v___y_5501_, v___y_5499_, v_ty_x3f_5483_, v_a_5480_, v_cont_5484_, v___y_5500_, v___y_5496_, v___y_5497_, v___y_5493_, v___y_5494_, v___y_5495_);
return v___x_5502_;
}
else
{
lean_object* v___x_5503_; 
lean_dec(v_ty_x3f_5483_);
v___x_5503_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5477_, v_fs_5478_, v_clears_5479_, v___y_5501_, v___y_5499_, v___y_5498_, v_a_5480_, v_cont_5484_, v___y_5500_, v___y_5496_, v___y_5497_, v___y_5493_, v___y_5494_, v___y_5495_);
return v___x_5503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5575_, lean_object* v_pats_5576_, lean_object* v_ty_x3f_5577_, lean_object* v_cont_5578_, lean_object* v_i_5579_, lean_object* v_g_5580_, lean_object* v_fs_5581_, lean_object* v_clears_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_){
_start:
{
lean_object* v___x_5591_; uint8_t v___x_5592_; 
v___x_5591_ = lean_array_get_size(v_pats_5576_);
v___x_5592_ = lean_nat_dec_lt(v_i_5579_, v___x_5591_);
if (v___x_5592_ == 0)
{
lean_object* v___x_5593_; 
lean_dec(v_ty_x3f_5577_);
lean_dec_ref(v_pats_5576_);
lean_dec(v_ref_5575_);
lean_inc(v_a_5589_);
lean_inc_ref(v_a_5588_);
lean_inc(v_a_5587_);
lean_inc_ref(v_a_5586_);
lean_inc(v_a_5585_);
lean_inc_ref(v_a_5584_);
v___x_5593_ = lean_apply_11(v_cont_5578_, v_g_5580_, v_fs_5581_, v_clears_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, lean_box(0));
return v___x_5593_;
}
else
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v___x_5594_ = lean_array_fget(v_pats_5576_, v_i_5579_);
v___x_5595_ = lean_unsigned_to_nat(1u);
v___x_5596_ = lean_nat_add(v_i_5579_, v___x_5595_);
lean_inc(v_ty_x3f_5577_);
lean_inc(v_ref_5575_);
v___x_5597_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5597_, 0, v_ref_5575_);
lean_closure_set(v___x_5597_, 1, v_pats_5576_);
lean_closure_set(v___x_5597_, 2, v_ty_x3f_5577_);
lean_closure_set(v___x_5597_, 3, v_cont_5578_);
lean_closure_set(v___x_5597_, 4, v___x_5596_);
v___x_5598_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5580_, v_fs_5581_, v_clears_5582_, v_a_5583_, v_ref_5575_, v___x_5594_, v_ty_x3f_5577_, v___x_5597_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
return v___x_5598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5599_, lean_object* v_ref_5600_, lean_object* v_pats_5601_, lean_object* v_ty_x3f_5602_, lean_object* v_cont_5603_, lean_object* v_i_5604_, lean_object* v_g_5605_, lean_object* v_fs_5606_, lean_object* v_clears_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v___x_5616_; 
v___x_5616_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5600_, v_pats_5601_, v_ty_x3f_5602_, v_cont_5603_, v_i_5604_, v_g_5605_, v_fs_5606_, v_clears_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_);
return v___x_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5617_, lean_object* v_fs_5618_, lean_object* v_clears_5619_, lean_object* v_ref_5620_, lean_object* v_pats_5621_, lean_object* v_ty_x3f_5622_, lean_object* v_a_5623_, lean_object* v_cont_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5617_, v_fs_5618_, v_clears_5619_, v_ref_5620_, v_pats_5621_, v_ty_x3f_5622_, v_a_5623_, v_cont_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_);
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
lean_dec(v_a_5628_);
lean_dec_ref(v_a_5627_);
lean_dec(v_a_5626_);
lean_dec_ref(v_a_5625_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5633_, lean_object* v_fs_5634_, lean_object* v_clears_5635_, lean_object* v_a_5636_, lean_object* v_ref_5637_, lean_object* v_pat_5638_, lean_object* v_ty_x3f_5639_, lean_object* v_cont_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5633_, v_fs_5634_, v_clears_5635_, v_a_5636_, v_ref_5637_, v_pat_5638_, v_ty_x3f_5639_, v_cont_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
lean_dec(v_a_5642_);
lean_dec_ref(v_a_5641_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_){
_start:
{
lean_object* v___x_5657_; 
v___x_5657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5667_, lean_object* v_g_5668_, lean_object* v_fs_5669_, lean_object* v_clears_5670_, lean_object* v_a_5671_, lean_object* v_ref_5672_, lean_object* v_pat_5673_, lean_object* v_ty_x3f_5674_, lean_object* v_cont_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v___x_5683_; 
v___x_5683_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5668_, v_fs_5669_, v_clears_5670_, v_a_5671_, v_ref_5672_, v_pat_5673_, v_ty_x3f_5674_, v_cont_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
return v___x_5683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5684_, lean_object* v_g_5685_, lean_object* v_fs_5686_, lean_object* v_clears_5687_, lean_object* v_a_5688_, lean_object* v_ref_5689_, lean_object* v_pat_5690_, lean_object* v_ty_x3f_5691_, lean_object* v_cont_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v_res_5700_; 
v_res_5700_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5684_, v_g_5685_, v_fs_5686_, v_clears_5687_, v_a_5688_, v_ref_5689_, v_pat_5690_, v_ty_x3f_5691_, v_cont_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_);
lean_dec(v_a_5698_);
lean_dec_ref(v_a_5697_);
lean_dec(v_a_5696_);
lean_dec_ref(v_a_5695_);
lean_dec(v_a_5694_);
lean_dec_ref(v_a_5693_);
return v_res_5700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5701_, lean_object* v_g_5702_, lean_object* v_fs_5703_, lean_object* v_clears_5704_, lean_object* v_ref_5705_, lean_object* v_pats_5706_, lean_object* v_ty_x3f_5707_, lean_object* v_a_5708_, lean_object* v_cont_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5702_, v_fs_5703_, v_clears_5704_, v_ref_5705_, v_pats_5706_, v_ty_x3f_5707_, v_a_5708_, v_cont_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5718_, lean_object* v_g_5719_, lean_object* v_fs_5720_, lean_object* v_clears_5721_, lean_object* v_ref_5722_, lean_object* v_pats_5723_, lean_object* v_ty_x3f_5724_, lean_object* v_a_5725_, lean_object* v_cont_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5718_, v_g_5719_, v_fs_5720_, v_clears_5721_, v_ref_5722_, v_pats_5723_, v_ty_x3f_5724_, v_a_5725_, v_cont_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_);
lean_dec(v_a_5732_);
lean_dec_ref(v_a_5731_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5735_, lean_object* v___x_5736_, lean_object* v___x_5737_, lean_object* v___x_5738_, lean_object* v_pats_5739_, lean_object* v_ty_x3f_5740_, lean_object* v___x_5741_, lean_object* v___x_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
lean_object* v___x_5750_; 
v___x_5750_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5735_, v___x_5736_, v___x_5737_, v___x_5738_, v_pats_5739_, v_ty_x3f_5740_, v___x_5741_, v___x_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5759_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5759_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5759_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5757_; 
v___x_5755_ = lean_array_to_list(v_a_5751_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5755_);
v___x_5757_ = v___x_5753_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v___x_5755_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
else
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5767_; 
v_a_5760_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5767_ == 0)
{
v___x_5762_ = v___x_5750_;
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5750_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5765_; 
if (v_isShared_5763_ == 0)
{
v___x_5765_ = v___x_5762_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5768_, lean_object* v___x_5769_, lean_object* v___x_5770_, lean_object* v___x_5771_, lean_object* v_pats_5772_, lean_object* v_ty_x3f_5773_, lean_object* v___x_5774_, lean_object* v___x_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5768_, v___x_5769_, v___x_5770_, v___x_5771_, v_pats_5772_, v_ty_x3f_5773_, v___x_5774_, v___x_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
lean_dec(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
lean_dec(v___y_5777_);
lean_dec_ref(v___y_5776_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5784_, lean_object* v_ty_x3f_5785_, lean_object* v_g_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___f_5798_; uint8_t v___x_5799_; lean_object* v___x_5800_; 
v___x_5794_ = lean_box(0);
v___x_5795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5796_ = lean_box(0);
v___x_5797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5798_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5798_, 0, v_g_5786_);
lean_closure_set(v___f_5798_, 1, v___x_5794_);
lean_closure_set(v___f_5798_, 2, v___x_5795_);
lean_closure_set(v___f_5798_, 3, v___x_5796_);
lean_closure_set(v___f_5798_, 4, v_pats_5784_);
lean_closure_set(v___f_5798_, 5, v_ty_x3f_5785_);
lean_closure_set(v___f_5798_, 6, v___x_5795_);
lean_closure_set(v___f_5798_, 7, v___x_5797_);
v___x_5799_ = 1;
v___x_5800_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5798_, v___x_5799_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5801_, lean_object* v_ty_x3f_5802_, lean_object* v_g_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5801_, v_ty_x3f_5802_, v_g_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
lean_dec(v_a_5805_);
lean_dec_ref(v_a_5804_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5814_, 0, v___x_5813_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_){
_start:
{
lean_object* v___x_5827_; 
v___x_5827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec(v___y_5834_);
lean_dec_ref(v___y_5833_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v___x_5849_; 
lean_inc(v___y_5843_);
lean_inc_ref(v___y_5842_);
lean_inc(v___y_5841_);
lean_inc_ref(v___y_5840_);
v___x_5849_ = lean_apply_9(v_x_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, lean_box(0));
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_){
_start:
{
lean_object* v_res_5860_; 
v_res_5860_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
return v_res_5860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5861_, lean_object* v_x_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v___f_5872_; lean_object* v___x_5873_; 
lean_inc(v___y_5866_);
lean_inc_ref(v___y_5865_);
lean_inc(v___y_5864_);
lean_inc_ref(v___y_5863_);
v___f_5872_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5872_, 0, v_x_5862_);
lean_closure_set(v___f_5872_, 1, v___y_5863_);
lean_closure_set(v___f_5872_, 2, v___y_5864_);
lean_closure_set(v___f_5872_, 3, v___y_5865_);
lean_closure_set(v___f_5872_, 4, v___y_5866_);
v___x_5873_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5861_, v___f_5872_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5873_) == 0)
{
return v___x_5873_;
}
else
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
v_a_5874_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5873_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5873_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5882_, lean_object* v_x_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5882_, v_x_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5886_);
lean_dec(v___y_5885_);
lean_dec_ref(v___y_5884_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5894_, lean_object* v_mvarId_5895_, lean_object* v_x_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_){
_start:
{
lean_object* v___x_5906_; 
v___x_5906_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5895_, v_x_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5907_, lean_object* v_mvarId_5908_, lean_object* v_x_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5907_, v_mvarId_5908_, v_x_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec_ref(v___y_5910_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5920_, lean_object* v_pat_5921_, lean_object* v_a_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_){
_start:
{
lean_object* v___x_5932_; 
v___x_5932_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5920_, v_pat_5921_, v_a_5922_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v_a_5933_; lean_object* v___x_5934_; 
v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5932_, 1);
v___x_5934_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5933_, v___y_5924_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
return v___x_5934_;
}
else
{
lean_object* v_a_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5942_; 
v_a_5935_ = lean_ctor_get(v___x_5932_, 0);
v_isSharedCheck_5942_ = !lean_is_exclusive(v___x_5932_);
if (v_isSharedCheck_5942_ == 0)
{
v___x_5937_ = v___x_5932_;
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_a_5935_);
lean_dec(v___x_5932_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5940_; 
if (v_isShared_5938_ == 0)
{
v___x_5940_ = v___x_5937_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_a_5935_);
v___x_5940_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
return v___x_5940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5943_, lean_object* v_pat_5944_, lean_object* v_a_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5943_, v_pat_5944_, v_a_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
lean_dec(v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec_ref(v___y_5946_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5956_, size_t v_i_5957_, lean_object* v_bs_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_){
_start:
{
uint8_t v___x_5963_; 
v___x_5963_ = lean_usize_dec_lt(v_i_5957_, v_sz_5956_);
if (v___x_5963_ == 0)
{
lean_object* v___x_5964_; 
v___x_5964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5964_, 0, v_bs_5958_);
return v___x_5964_;
}
else
{
lean_object* v_v_5965_; lean_object* v___x_5966_; lean_object* v_bs_x27_5967_; lean_object* v___x_5968_; 
v_v_5965_ = lean_array_uget(v_bs_5958_, v_i_5957_);
v___x_5966_ = lean_unsigned_to_nat(0u);
v_bs_x27_5967_ = lean_array_uset(v_bs_5958_, v_i_5957_, v___x_5966_);
v___x_5968_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_5965_, v___y_5959_, v___y_5960_, v___y_5961_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v_hIdent_x3f_5970_; lean_object* v_term_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5982_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v_hIdent_x3f_5970_ = lean_ctor_get(v_a_5969_, 0);
v_term_5971_ = lean_ctor_get(v_a_5969_, 1);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_a_5969_);
if (v_isSharedCheck_5982_ == 0)
{
v___x_5973_ = v_a_5969_;
v_isShared_5974_ = v_isSharedCheck_5982_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_term_5971_);
lean_inc(v_hIdent_x3f_5970_);
lean_dec(v_a_5969_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5982_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5974_ == 0)
{
v___x_5976_ = v___x_5973_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_hIdent_x3f_5970_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v_term_5971_);
v___x_5976_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
size_t v___x_5977_; size_t v___x_5978_; lean_object* v___x_5979_; 
v___x_5977_ = ((size_t)1ULL);
v___x_5978_ = lean_usize_add(v_i_5957_, v___x_5977_);
v___x_5979_ = lean_array_uset(v_bs_x27_5967_, v_i_5957_, v___x_5976_);
v_i_5957_ = v___x_5978_;
v_bs_5958_ = v___x_5979_;
goto _start;
}
}
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec_ref(v_bs_x27_5967_);
v_a_5983_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5968_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5968_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_5991_, lean_object* v_i_5992_, lean_object* v_bs_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
size_t v_sz_boxed_5998_; size_t v_i_boxed_5999_; lean_object* v_res_6000_; 
v_sz_boxed_5998_ = lean_unbox_usize(v_sz_5991_);
lean_dec(v_sz_5991_);
v_i_boxed_5999_ = lean_unbox_usize(v_i_5992_);
lean_dec(v_i_5992_);
v_res_6000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_5998_, v_i_boxed_5999_, v_bs_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec_ref(v___y_5994_);
return v_res_6000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_){
_start:
{
lean_object* v___y_6018_; lean_object* v_pat_6019_; lean_object* v___y_6020_; lean_object* v___y_6021_; lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v___y_6026_; lean_object* v___y_6027_; lean_object* v___x_6053_; uint8_t v___x_6054_; 
v___x_6053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_6007_);
v___x_6054_ = l_Lean_Syntax_isOfKind(v_stx_6007_, v___x_6053_);
if (v___x_6054_ == 0)
{
lean_object* v___x_6055_; 
lean_dec(v_stx_6007_);
v___x_6055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6055_;
}
else
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; uint8_t v___x_6060_; 
v___x_6056_ = lean_unsigned_to_nat(1u);
v___x_6057_ = l_Lean_Syntax_getArg(v_stx_6007_, v___x_6056_);
v___x_6058_ = lean_unsigned_to_nat(2u);
v___x_6059_ = l_Lean_Syntax_getArg(v_stx_6007_, v___x_6058_);
v___x_6060_ = l_Lean_Syntax_isNone(v___x_6059_);
if (v___x_6060_ == 0)
{
uint8_t v___x_6061_; 
lean_dec(v_stx_6007_);
lean_inc(v___x_6059_);
v___x_6061_ = l_Lean_Syntax_matchesNull(v___x_6059_, v___x_6058_);
if (v___x_6061_ == 0)
{
lean_object* v___x_6062_; 
lean_dec(v___x_6059_);
lean_dec(v___x_6057_);
v___x_6062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6062_;
}
else
{
lean_object* v_pat_x3f_6063_; lean_object* v_tgts_6064_; lean_object* v___x_6065_; 
v_pat_x3f_6063_ = l_Lean_Syntax_getArg(v___x_6059_, v___x_6056_);
lean_dec(v___x_6059_);
v_tgts_6064_ = l_Lean_Syntax_getArgs(v___x_6057_);
lean_dec(v___x_6057_);
v___x_6065_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6063_, v_a_6012_, v_a_6013_, v_a_6014_, v_a_6015_);
if (lean_obj_tag(v___x_6065_) == 0)
{
lean_object* v_a_6066_; 
v_a_6066_ = lean_ctor_get(v___x_6065_, 0);
lean_inc(v_a_6066_);
lean_dec_ref_known(v___x_6065_, 1);
v___y_6018_ = v_tgts_6064_;
v_pat_6019_ = v_a_6066_;
v___y_6020_ = v_a_6008_;
v___y_6021_ = v_a_6009_;
v___y_6022_ = v_a_6010_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
v___y_6025_ = v_a_6013_;
v___y_6026_ = v_a_6014_;
v___y_6027_ = v_a_6015_;
goto v___jp_6017_;
}
else
{
lean_object* v_a_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6074_; 
lean_dec_ref(v_tgts_6064_);
v_a_6067_ = lean_ctor_get(v___x_6065_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v___x_6065_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6069_ = v___x_6065_;
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_a_6067_);
lean_dec(v___x_6065_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6072_; 
if (v_isShared_6070_ == 0)
{
v___x_6072_ = v___x_6069_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v_a_6067_);
v___x_6072_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
return v___x_6072_;
}
}
}
}
}
else
{
lean_object* v___x_6075_; lean_object* v_tk_6076_; lean_object* v_tgts_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
lean_dec(v___x_6059_);
v___x_6075_ = lean_unsigned_to_nat(0u);
v_tk_6076_ = l_Lean_Syntax_getArg(v_stx_6007_, v___x_6075_);
lean_dec(v_stx_6007_);
v_tgts_6077_ = l_Lean_Syntax_getArgs(v___x_6057_);
lean_dec(v___x_6057_);
v___x_6078_ = lean_box(0);
v___x_6079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6079_, 0, v_tk_6076_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___y_6018_ = v_tgts_6077_;
v_pat_6019_ = v___x_6079_;
v___y_6020_ = v_a_6008_;
v___y_6021_ = v_a_6009_;
v___y_6022_ = v_a_6010_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
v___y_6025_ = v_a_6013_;
v___y_6026_ = v_a_6014_;
v___y_6027_ = v_a_6015_;
goto v___jp_6017_;
}
}
v___jp_6017_:
{
lean_object* v___x_6028_; size_t v_sz_6029_; size_t v___x_6030_; lean_object* v___x_6031_; 
v___x_6028_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6018_);
lean_dec_ref(v___y_6018_);
v_sz_6029_ = lean_array_size(v___x_6028_);
v___x_6030_ = ((size_t)0ULL);
v___x_6031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6029_, v___x_6030_, v___x_6028_, v___y_6024_, v___y_6026_, v___y_6027_);
if (lean_obj_tag(v___x_6031_) == 0)
{
lean_object* v_a_6032_; lean_object* v___x_6033_; 
v_a_6032_ = lean_ctor_get(v___x_6031_, 0);
lean_inc(v_a_6032_);
lean_dec_ref_known(v___x_6031_, 1);
v___x_6033_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6021_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
if (lean_obj_tag(v___x_6033_) == 0)
{
lean_object* v_a_6034_; lean_object* v___f_6035_; lean_object* v___x_6036_; 
v_a_6034_ = lean_ctor_get(v___x_6033_, 0);
lean_inc_n(v_a_6034_, 2);
lean_dec_ref_known(v___x_6033_, 1);
v___f_6035_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6035_, 0, v_a_6032_);
lean_closure_set(v___f_6035_, 1, v_pat_6019_);
lean_closure_set(v___f_6035_, 2, v_a_6034_);
v___x_6036_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6034_, v___f_6035_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
return v___x_6036_;
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6044_; 
lean_dec(v_a_6032_);
lean_dec_ref(v_pat_6019_);
v_a_6037_ = lean_ctor_get(v___x_6033_, 0);
v_isSharedCheck_6044_ = !lean_is_exclusive(v___x_6033_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6039_ = v___x_6033_;
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_a_6037_);
lean_dec(v___x_6033_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v___x_6042_; 
if (v_isShared_6040_ == 0)
{
v___x_6042_ = v___x_6039_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
else
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6052_; 
lean_dec_ref(v_pat_6019_);
v_a_6045_ = lean_ctor_get(v___x_6031_, 0);
v_isSharedCheck_6052_ = !lean_is_exclusive(v___x_6031_);
if (v_isSharedCheck_6052_ == 0)
{
v___x_6047_ = v___x_6031_;
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v___x_6031_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6050_; 
if (v_isShared_6048_ == 0)
{
v___x_6050_ = v___x_6047_;
goto v_reusejp_6049_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
v___x_6050_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6049_;
}
v_reusejp_6049_:
{
return v___x_6050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_){
_start:
{
lean_object* v_res_6090_; 
v_res_6090_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_);
lean_dec(v_a_6088_);
lean_dec_ref(v_a_6087_);
lean_dec(v_a_6086_);
lean_dec_ref(v_a_6085_);
lean_dec(v_a_6084_);
lean_dec_ref(v_a_6083_);
lean_dec(v_a_6082_);
lean_dec_ref(v_a_6081_);
return v_res_6090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6091_, size_t v_i_6092_, lean_object* v_bs_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v___x_6103_; 
v___x_6103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6091_, v_i_6092_, v_bs_6093_, v___y_6098_, v___y_6100_, v___y_6101_);
return v___x_6103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6104_, lean_object* v_i_6105_, lean_object* v_bs_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
size_t v_sz_boxed_6116_; size_t v_i_boxed_6117_; lean_object* v_res_6118_; 
v_sz_boxed_6116_ = lean_unbox_usize(v_sz_6104_);
lean_dec(v_sz_6104_);
v_i_boxed_6117_ = lean_unbox_usize(v_i_6105_);
lean_dec(v_i_6105_);
v_res_6118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6116_, v_i_boxed_6117_, v_bs_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
return v_res_6118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6155_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6158_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6159_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6155_, v___x_6156_, v___x_6157_, v___x_6158_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6160_){
_start:
{
lean_object* v_res_6161_; 
v_res_6161_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6162_, lean_object* v___x_6163_, lean_object* v_a_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
lean_object* v___x_6174_; 
v___x_6174_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6162_, v___x_6163_, v_a_6164_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_);
if (lean_obj_tag(v___x_6174_) == 0)
{
lean_object* v_a_6175_; lean_object* v___x_6176_; 
v_a_6175_ = lean_ctor_get(v___x_6174_, 0);
lean_inc(v_a_6175_);
lean_dec_ref_known(v___x_6174_, 1);
v___x_6176_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6175_, v___y_6166_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_);
return v___x_6176_;
}
else
{
lean_object* v_a_6177_; lean_object* v___x_6179_; uint8_t v_isShared_6180_; uint8_t v_isSharedCheck_6184_; 
v_a_6177_ = lean_ctor_get(v___x_6174_, 0);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6174_);
if (v_isSharedCheck_6184_ == 0)
{
v___x_6179_ = v___x_6174_;
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
else
{
lean_inc(v_a_6177_);
lean_dec(v___x_6174_);
v___x_6179_ = lean_box(0);
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
v_resetjp_6178_:
{
lean_object* v___x_6182_; 
if (v_isShared_6180_ == 0)
{
v___x_6182_ = v___x_6179_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
v___x_6182_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
return v___x_6182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6185_, lean_object* v___x_6186_, lean_object* v_a_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_){
_start:
{
lean_object* v_res_6197_; 
v_res_6197_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6185_, v___x_6186_, v_a_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6191_);
lean_dec_ref(v___y_6190_);
lean_dec(v___y_6189_);
lean_dec_ref(v___y_6188_);
return v_res_6197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6198_, lean_object* v_val_6199_, lean_object* v_a_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6198_, v_val_6199_, v_a_6200_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_);
if (lean_obj_tag(v___x_6210_) == 0)
{
lean_object* v_a_6211_; lean_object* v___x_6212_; 
v_a_6211_ = lean_ctor_get(v___x_6210_, 0);
lean_inc(v_a_6211_);
lean_dec_ref_known(v___x_6210_, 1);
v___x_6212_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6211_, v___y_6202_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_);
return v___x_6212_;
}
else
{
lean_object* v_a_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6220_; 
v_a_6213_ = lean_ctor_get(v___x_6210_, 0);
v_isSharedCheck_6220_ = !lean_is_exclusive(v___x_6210_);
if (v_isSharedCheck_6220_ == 0)
{
v___x_6215_ = v___x_6210_;
v_isShared_6216_ = v_isSharedCheck_6220_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_a_6213_);
lean_dec(v___x_6210_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6220_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v___x_6218_; 
if (v_isShared_6216_ == 0)
{
v___x_6218_ = v___x_6215_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6219_; 
v_reuseFailAlloc_6219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6219_, 0, v_a_6213_);
v___x_6218_ = v_reuseFailAlloc_6219_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
return v___x_6218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6221_, lean_object* v_val_6222_, lean_object* v_a_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
lean_object* v_res_6233_; 
v_res_6233_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6221_, v_val_6222_, v_a_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
lean_dec(v___y_6225_);
lean_dec_ref(v___y_6224_);
return v_res_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
lean_object* v_ref_6240_; lean_object* v___x_6241_; lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6250_; 
v_ref_6240_ = lean_ctor_get(v___y_6237_, 2);
v___x_6241_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
v_a_6242_ = lean_ctor_get(v___x_6241_, 0);
v_isSharedCheck_6250_ = !lean_is_exclusive(v___x_6241_);
if (v_isSharedCheck_6250_ == 0)
{
v___x_6244_ = v___x_6241_;
v_isShared_6245_ = v_isSharedCheck_6250_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6241_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6250_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6246_; lean_object* v___x_6248_; 
lean_inc(v_ref_6240_);
v___x_6246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6246_, 0, v_ref_6240_);
lean_ctor_set(v___x_6246_, 1, v_a_6242_);
if (v_isShared_6245_ == 0)
{
lean_ctor_set_tag(v___x_6244_, 1);
lean_ctor_set(v___x_6244_, 0, v___x_6246_);
v___x_6248_ = v___x_6244_;
goto v_reusejp_6247_;
}
else
{
lean_object* v_reuseFailAlloc_6249_; 
v_reuseFailAlloc_6249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6249_, 0, v___x_6246_);
v___x_6248_ = v_reuseFailAlloc_6249_;
goto v_reusejp_6247_;
}
v_reusejp_6247_:
{
return v___x_6248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
lean_object* v_res_6257_; 
v_res_6257_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
return v_res_6257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6258_, size_t v_i_6259_, lean_object* v_bs_6260_){
_start:
{
uint8_t v___x_6261_; 
v___x_6261_ = lean_usize_dec_lt(v_i_6259_, v_sz_6258_);
if (v___x_6261_ == 0)
{
return v_bs_6260_;
}
else
{
lean_object* v_v_6262_; lean_object* v___x_6263_; lean_object* v_bs_x27_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; size_t v___x_6267_; size_t v___x_6268_; lean_object* v___x_6269_; 
v_v_6262_ = lean_array_uget(v_bs_6260_, v_i_6259_);
v___x_6263_ = lean_unsigned_to_nat(0u);
v_bs_x27_6264_ = lean_array_uset(v_bs_6260_, v_i_6259_, v___x_6263_);
v___x_6265_ = lean_box(0);
v___x_6266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6266_, 0, v___x_6265_);
lean_ctor_set(v___x_6266_, 1, v_v_6262_);
v___x_6267_ = ((size_t)1ULL);
v___x_6268_ = lean_usize_add(v_i_6259_, v___x_6267_);
v___x_6269_ = lean_array_uset(v_bs_x27_6264_, v_i_6259_, v___x_6266_);
v_i_6259_ = v___x_6268_;
v_bs_6260_ = v___x_6269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6271_, lean_object* v_i_6272_, lean_object* v_bs_6273_){
_start:
{
size_t v_sz_boxed_6274_; size_t v_i_boxed_6275_; lean_object* v_res_6276_; 
v_sz_boxed_6274_ = lean_unbox_usize(v_sz_6271_);
lean_dec(v_sz_6271_);
v_i_boxed_6275_ = lean_unbox_usize(v_i_6272_);
lean_dec(v_i_6272_);
v_res_6276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6274_, v_i_boxed_6275_, v_bs_6273_);
return v_res_6276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; 
v___x_6287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6288_ = l_Lean_stringToMessageData(v___x_6287_);
return v___x_6288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_, lean_object* v_a_6297_){
_start:
{
lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6307_; lean_object* v___y_6308_; lean_object* v___y_6309_; lean_object* v___x_6322_; uint8_t v___x_6323_; 
v___x_6322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6289_);
v___x_6323_ = l_Lean_Syntax_isOfKind(v_stx_6289_, v___x_6322_);
if (v___x_6323_ == 0)
{
lean_object* v___x_6324_; 
lean_dec(v_stx_6289_);
v___x_6324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6324_;
}
else
{
lean_object* v___x_6325_; lean_object* v_tk_6326_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v_a_6367_; lean_object* v___y_6381_; lean_object* v___y_6382_; lean_object* v_val_x3f_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v___x_6411_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v_ty_x3f_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v_pat_x3f_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; lean_object* v___y_6437_; lean_object* v___y_6438_; lean_object* v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v___x_6451_; uint8_t v___x_6452_; 
v___x_6325_ = lean_unsigned_to_nat(0u);
v_tk_6326_ = l_Lean_Syntax_getArg(v_stx_6289_, v___x_6325_);
v___x_6411_ = lean_unsigned_to_nat(1u);
v___x_6451_ = l_Lean_Syntax_getArg(v_stx_6289_, v___x_6411_);
v___x_6452_ = l_Lean_Syntax_isNone(v___x_6451_);
if (v___x_6452_ == 0)
{
uint8_t v___x_6453_; 
lean_inc(v___x_6451_);
v___x_6453_ = l_Lean_Syntax_matchesNull(v___x_6451_, v___x_6411_);
if (v___x_6453_ == 0)
{
lean_object* v___x_6454_; 
lean_dec(v___x_6451_);
lean_dec(v_tk_6326_);
lean_dec(v_stx_6289_);
v___x_6454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6454_;
}
else
{
lean_object* v_pat_x3f_6455_; 
v_pat_x3f_6455_ = l_Lean_Syntax_getArg(v___x_6451_, v___x_6325_);
lean_dec(v___x_6451_);
if (v___x_6452_ == 0)
{
lean_object* v___x_6458_; uint8_t v___x_6459_; 
v___x_6458_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6455_);
v___x_6459_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6455_, v___x_6458_);
if (v___x_6459_ == 0)
{
lean_object* v___x_6460_; 
lean_dec(v_pat_x3f_6455_);
lean_dec(v_tk_6326_);
lean_dec(v_stx_6289_);
v___x_6460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6460_;
}
else
{
goto v___jp_6456_;
}
}
else
{
goto v___jp_6456_;
}
v___jp_6456_:
{
lean_object* v___x_6457_; 
v___x_6457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6457_, 0, v_pat_x3f_6455_);
v_pat_x3f_6434_ = v___x_6457_;
v___y_6435_ = v_a_6290_;
v___y_6436_ = v_a_6291_;
v___y_6437_ = v_a_6292_;
v___y_6438_ = v_a_6293_;
v___y_6439_ = v_a_6294_;
v___y_6440_ = v_a_6295_;
v___y_6441_ = v_a_6296_;
v___y_6442_ = v_a_6297_;
goto v___jp_6433_;
}
}
}
else
{
lean_object* v___x_6461_; 
lean_dec(v___x_6451_);
v___x_6461_ = lean_box(0);
v_pat_x3f_6434_ = v___x_6461_;
v___y_6435_ = v_a_6290_;
v___y_6436_ = v_a_6291_;
v___y_6437_ = v_a_6292_;
v___y_6438_ = v_a_6293_;
v___y_6439_ = v_a_6294_;
v___y_6440_ = v_a_6295_;
v___y_6441_ = v_a_6296_;
v___y_6442_ = v_a_6297_;
goto v___jp_6433_;
}
v___jp_6327_:
{
lean_object* v___x_6339_; lean_object* v___x_6340_; size_t v_sz_6341_; size_t v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6339_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6326_, v___y_6338_, v___y_6337_);
lean_dec(v___y_6337_);
v___x_6340_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6336_);
lean_dec_ref(v___y_6336_);
v_sz_6341_ = lean_array_size(v___x_6340_);
v___x_6342_ = ((size_t)0ULL);
v___x_6343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6341_, v___x_6342_, v___x_6340_);
v___x_6344_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6333_, v___y_6332_, v___y_6330_, v___y_6335_, v___y_6331_);
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; lean_object* v___f_6346_; lean_object* v___x_6347_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
lean_inc_n(v_a_6345_, 2);
lean_dec_ref_known(v___x_6344_, 1);
v___f_6346_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6346_, 0, v___x_6343_);
lean_closure_set(v___f_6346_, 1, v___x_6339_);
lean_closure_set(v___f_6346_, 2, v_a_6345_);
v___x_6347_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6345_, v___f_6346_, v___y_6329_, v___y_6333_, v___y_6334_, v___y_6328_, v___y_6332_, v___y_6330_, v___y_6335_, v___y_6331_);
return v___x_6347_;
}
else
{
lean_object* v_a_6348_; lean_object* v___x_6350_; uint8_t v_isShared_6351_; uint8_t v_isSharedCheck_6355_; 
lean_dec_ref(v___x_6343_);
lean_dec_ref(v___x_6339_);
v_a_6348_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6355_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6355_ == 0)
{
v___x_6350_ = v___x_6344_;
v_isShared_6351_ = v_isSharedCheck_6355_;
goto v_resetjp_6349_;
}
else
{
lean_inc(v_a_6348_);
lean_dec(v___x_6344_);
v___x_6350_ = lean_box(0);
v_isShared_6351_ = v_isSharedCheck_6355_;
goto v_resetjp_6349_;
}
v_resetjp_6349_:
{
lean_object* v___x_6353_; 
if (v_isShared_6351_ == 0)
{
v___x_6353_ = v___x_6350_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_a_6348_);
v___x_6353_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
return v___x_6353_;
}
}
}
}
v___jp_6356_:
{
if (lean_obj_tag(v___y_6365_) == 1)
{
if (lean_obj_tag(v_a_6367_) == 0)
{
lean_object* v_val_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; 
v_val_6368_ = lean_ctor_get(v___y_6365_, 0);
lean_inc(v_val_6368_);
lean_dec_ref_known(v___y_6365_, 1);
v___x_6369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6326_);
v___x_6370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6370_, 0, v_tk_6326_);
lean_ctor_set(v___x_6370_, 1, v___x_6369_);
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6359_;
v___y_6330_ = v___y_6358_;
v___y_6331_ = v___y_6360_;
v___y_6332_ = v___y_6362_;
v___y_6333_ = v___y_6361_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6363_;
v___y_6336_ = v_val_6368_;
v___y_6337_ = v___y_6366_;
v___y_6338_ = v___x_6370_;
goto v___jp_6327_;
}
else
{
lean_object* v_val_6371_; lean_object* v_val_6372_; 
v_val_6371_ = lean_ctor_get(v___y_6365_, 0);
lean_inc(v_val_6371_);
lean_dec_ref_known(v___y_6365_, 1);
v_val_6372_ = lean_ctor_get(v_a_6367_, 0);
lean_inc(v_val_6372_);
lean_dec_ref_known(v_a_6367_, 1);
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6359_;
v___y_6330_ = v___y_6358_;
v___y_6331_ = v___y_6360_;
v___y_6332_ = v___y_6362_;
v___y_6333_ = v___y_6361_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6363_;
v___y_6336_ = v_val_6371_;
v___y_6337_ = v___y_6366_;
v___y_6338_ = v_val_6372_;
goto v___jp_6327_;
}
}
else
{
lean_dec(v___y_6365_);
if (lean_obj_tag(v___y_6366_) == 1)
{
if (lean_obj_tag(v_a_6367_) == 0)
{
lean_object* v_val_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v_val_6373_ = lean_ctor_get(v___y_6366_, 0);
lean_inc(v_val_6373_);
lean_dec_ref_known(v___y_6366_, 1);
v___x_6374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6375_, 0, v_tk_6326_);
lean_ctor_set(v___x_6375_, 1, v___x_6374_);
v___y_6300_ = v_val_6373_;
v___y_6301_ = v___y_6357_;
v___y_6302_ = v___y_6359_;
v___y_6303_ = v___y_6358_;
v___y_6304_ = v___y_6360_;
v___y_6305_ = v___y_6362_;
v___y_6306_ = v___y_6361_;
v___y_6307_ = v___y_6364_;
v___y_6308_ = v___y_6363_;
v___y_6309_ = v___x_6375_;
goto v___jp_6299_;
}
else
{
lean_object* v_val_6376_; lean_object* v_val_6377_; 
lean_dec(v_tk_6326_);
v_val_6376_ = lean_ctor_get(v___y_6366_, 0);
lean_inc(v_val_6376_);
lean_dec_ref_known(v___y_6366_, 1);
v_val_6377_ = lean_ctor_get(v_a_6367_, 0);
lean_inc(v_val_6377_);
lean_dec_ref_known(v_a_6367_, 1);
v___y_6300_ = v_val_6376_;
v___y_6301_ = v___y_6357_;
v___y_6302_ = v___y_6359_;
v___y_6303_ = v___y_6358_;
v___y_6304_ = v___y_6360_;
v___y_6305_ = v___y_6362_;
v___y_6306_ = v___y_6361_;
v___y_6307_ = v___y_6364_;
v___y_6308_ = v___y_6363_;
v___y_6309_ = v_val_6377_;
goto v___jp_6299_;
}
}
else
{
lean_object* v___x_6378_; lean_object* v___x_6379_; 
lean_dec(v_a_6367_);
lean_dec(v___y_6366_);
lean_dec(v_tk_6326_);
v___x_6378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6379_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6378_, v___y_6362_, v___y_6358_, v___y_6363_, v___y_6360_);
return v___x_6379_;
}
}
}
v___jp_6380_:
{
if (lean_obj_tag(v___y_6381_) == 0)
{
lean_object* v___x_6392_; 
v___x_6392_ = lean_box(0);
v___y_6357_ = v___y_6387_;
v___y_6358_ = v___y_6389_;
v___y_6359_ = v___y_6384_;
v___y_6360_ = v___y_6391_;
v___y_6361_ = v___y_6385_;
v___y_6362_ = v___y_6388_;
v___y_6363_ = v___y_6390_;
v___y_6364_ = v___y_6386_;
v___y_6365_ = v_val_x3f_6383_;
v___y_6366_ = v___y_6382_;
v_a_6367_ = v___x_6392_;
goto v___jp_6356_;
}
else
{
lean_object* v_val_6393_; lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6410_; 
v_val_6393_ = lean_ctor_get(v___y_6381_, 0);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___y_6381_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6395_ = v___y_6381_;
v_isShared_6396_ = v_isSharedCheck_6410_;
goto v_resetjp_6394_;
}
else
{
lean_inc(v_val_6393_);
lean_dec(v___y_6381_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6410_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
lean_object* v___x_6397_; 
v___x_6397_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6393_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_);
if (lean_obj_tag(v___x_6397_) == 0)
{
lean_object* v_a_6398_; lean_object* v___x_6400_; 
v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
lean_inc(v_a_6398_);
lean_dec_ref_known(v___x_6397_, 1);
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 0, v_a_6398_);
v___x_6400_ = v___x_6395_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6398_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
v___y_6357_ = v___y_6387_;
v___y_6358_ = v___y_6389_;
v___y_6359_ = v___y_6384_;
v___y_6360_ = v___y_6391_;
v___y_6361_ = v___y_6385_;
v___y_6362_ = v___y_6388_;
v___y_6363_ = v___y_6390_;
v___y_6364_ = v___y_6386_;
v___y_6365_ = v_val_x3f_6383_;
v___y_6366_ = v___y_6382_;
v_a_6367_ = v___x_6400_;
goto v___jp_6356_;
}
}
else
{
lean_object* v_a_6402_; lean_object* v___x_6404_; uint8_t v_isShared_6405_; uint8_t v_isSharedCheck_6409_; 
lean_del_object(v___x_6395_);
lean_dec(v_val_x3f_6383_);
lean_dec(v___y_6382_);
lean_dec(v_tk_6326_);
v_a_6402_ = lean_ctor_get(v___x_6397_, 0);
v_isSharedCheck_6409_ = !lean_is_exclusive(v___x_6397_);
if (v_isSharedCheck_6409_ == 0)
{
v___x_6404_ = v___x_6397_;
v_isShared_6405_ = v_isSharedCheck_6409_;
goto v_resetjp_6403_;
}
else
{
lean_inc(v_a_6402_);
lean_dec(v___x_6397_);
v___x_6404_ = lean_box(0);
v_isShared_6405_ = v_isSharedCheck_6409_;
goto v_resetjp_6403_;
}
v_resetjp_6403_:
{
lean_object* v___x_6407_; 
if (v_isShared_6405_ == 0)
{
v___x_6407_ = v___x_6404_;
goto v_reusejp_6406_;
}
else
{
lean_object* v_reuseFailAlloc_6408_; 
v_reuseFailAlloc_6408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6408_, 0, v_a_6402_);
v___x_6407_ = v_reuseFailAlloc_6408_;
goto v_reusejp_6406_;
}
v_reusejp_6406_:
{
return v___x_6407_;
}
}
}
}
}
}
v___jp_6412_:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; uint8_t v___x_6426_; 
v___x_6424_ = lean_unsigned_to_nat(3u);
v___x_6425_ = l_Lean_Syntax_getArg(v_stx_6289_, v___x_6424_);
lean_dec(v_stx_6289_);
v___x_6426_ = l_Lean_Syntax_isNone(v___x_6425_);
if (v___x_6426_ == 0)
{
uint8_t v___x_6427_; 
lean_inc(v___x_6425_);
v___x_6427_ = l_Lean_Syntax_matchesNull(v___x_6425_, v___y_6414_);
if (v___x_6427_ == 0)
{
lean_object* v___x_6428_; 
lean_dec(v___x_6425_);
lean_dec(v_ty_x3f_6415_);
lean_dec(v___y_6413_);
lean_dec(v_tk_6326_);
v___x_6428_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6428_;
}
else
{
lean_object* v___x_6429_; lean_object* v_val_x3f_6430_; lean_object* v___x_6431_; 
v___x_6429_ = l_Lean_Syntax_getArg(v___x_6425_, v___x_6411_);
lean_dec(v___x_6425_);
v_val_x3f_6430_ = l_Lean_Syntax_getArgs(v___x_6429_);
lean_dec(v___x_6429_);
v___x_6431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6431_, 0, v_val_x3f_6430_);
v___y_6381_ = v___y_6413_;
v___y_6382_ = v_ty_x3f_6415_;
v_val_x3f_6383_ = v___x_6431_;
v___y_6384_ = v___y_6416_;
v___y_6385_ = v___y_6417_;
v___y_6386_ = v___y_6418_;
v___y_6387_ = v___y_6419_;
v___y_6388_ = v___y_6420_;
v___y_6389_ = v___y_6421_;
v___y_6390_ = v___y_6422_;
v___y_6391_ = v___y_6423_;
goto v___jp_6380_;
}
}
else
{
lean_object* v___x_6432_; 
lean_dec(v___x_6425_);
v___x_6432_ = lean_box(0);
v___y_6381_ = v___y_6413_;
v___y_6382_ = v_ty_x3f_6415_;
v_val_x3f_6383_ = v___x_6432_;
v___y_6384_ = v___y_6416_;
v___y_6385_ = v___y_6417_;
v___y_6386_ = v___y_6418_;
v___y_6387_ = v___y_6419_;
v___y_6388_ = v___y_6420_;
v___y_6389_ = v___y_6421_;
v___y_6390_ = v___y_6422_;
v___y_6391_ = v___y_6423_;
goto v___jp_6380_;
}
}
v___jp_6433_:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; uint8_t v___x_6445_; 
v___x_6443_ = lean_unsigned_to_nat(2u);
v___x_6444_ = l_Lean_Syntax_getArg(v_stx_6289_, v___x_6443_);
v___x_6445_ = l_Lean_Syntax_isNone(v___x_6444_);
if (v___x_6445_ == 0)
{
uint8_t v___x_6446_; 
lean_inc(v___x_6444_);
v___x_6446_ = l_Lean_Syntax_matchesNull(v___x_6444_, v___x_6443_);
if (v___x_6446_ == 0)
{
lean_object* v___x_6447_; 
lean_dec(v___x_6444_);
lean_dec(v_pat_x3f_6434_);
lean_dec(v_tk_6326_);
lean_dec(v_stx_6289_);
v___x_6447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6447_;
}
else
{
lean_object* v_ty_x3f_6448_; lean_object* v___x_6449_; 
v_ty_x3f_6448_ = l_Lean_Syntax_getArg(v___x_6444_, v___x_6411_);
lean_dec(v___x_6444_);
v___x_6449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6449_, 0, v_ty_x3f_6448_);
v___y_6413_ = v_pat_x3f_6434_;
v___y_6414_ = v___x_6443_;
v_ty_x3f_6415_ = v___x_6449_;
v___y_6416_ = v___y_6435_;
v___y_6417_ = v___y_6436_;
v___y_6418_ = v___y_6437_;
v___y_6419_ = v___y_6438_;
v___y_6420_ = v___y_6439_;
v___y_6421_ = v___y_6440_;
v___y_6422_ = v___y_6441_;
v___y_6423_ = v___y_6442_;
goto v___jp_6412_;
}
}
else
{
lean_object* v___x_6450_; 
lean_dec(v___x_6444_);
v___x_6450_ = lean_box(0);
v___y_6413_ = v_pat_x3f_6434_;
v___y_6414_ = v___x_6443_;
v_ty_x3f_6415_ = v___x_6450_;
v___y_6416_ = v___y_6435_;
v___y_6417_ = v___y_6436_;
v___y_6418_ = v___y_6437_;
v___y_6419_ = v___y_6438_;
v___y_6420_ = v___y_6439_;
v___y_6421_ = v___y_6440_;
v___y_6422_ = v___y_6441_;
v___y_6423_ = v___y_6442_;
goto v___jp_6412_;
}
}
}
v___jp_6299_:
{
lean_object* v___x_6310_; 
v___x_6310_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6306_, v___y_6305_, v___y_6303_, v___y_6308_, v___y_6304_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_object* v_a_6311_; lean_object* v___f_6312_; lean_object* v___x_6313_; 
v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
lean_inc_n(v_a_6311_, 2);
lean_dec_ref_known(v___x_6310_, 1);
v___f_6312_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6312_, 0, v___y_6309_);
lean_closure_set(v___f_6312_, 1, v___y_6300_);
lean_closure_set(v___f_6312_, 2, v_a_6311_);
v___x_6313_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6311_, v___f_6312_, v___y_6302_, v___y_6306_, v___y_6307_, v___y_6301_, v___y_6305_, v___y_6303_, v___y_6308_, v___y_6304_);
return v___x_6313_;
}
else
{
lean_object* v_a_6314_; lean_object* v___x_6316_; uint8_t v_isShared_6317_; uint8_t v_isSharedCheck_6321_; 
lean_dec_ref(v___y_6309_);
lean_dec(v___y_6300_);
v_a_6314_ = lean_ctor_get(v___x_6310_, 0);
v_isSharedCheck_6321_ = !lean_is_exclusive(v___x_6310_);
if (v_isSharedCheck_6321_ == 0)
{
v___x_6316_ = v___x_6310_;
v_isShared_6317_ = v_isSharedCheck_6321_;
goto v_resetjp_6315_;
}
else
{
lean_inc(v_a_6314_);
lean_dec(v___x_6310_);
v___x_6316_ = lean_box(0);
v_isShared_6317_ = v_isSharedCheck_6321_;
goto v_resetjp_6315_;
}
v_resetjp_6315_:
{
lean_object* v___x_6319_; 
if (v_isShared_6317_ == 0)
{
v___x_6319_ = v___x_6316_;
goto v_reusejp_6318_;
}
else
{
lean_object* v_reuseFailAlloc_6320_; 
v_reuseFailAlloc_6320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6314_);
v___x_6319_ = v_reuseFailAlloc_6320_;
goto v_reusejp_6318_;
}
v_reusejp_6318_:
{
return v___x_6319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_, lean_object* v_a_6469_, lean_object* v_a_6470_, lean_object* v_a_6471_){
_start:
{
lean_object* v_res_6472_; 
v_res_6472_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_, v_a_6469_, v_a_6470_);
lean_dec(v_a_6470_);
lean_dec_ref(v_a_6469_);
lean_dec(v_a_6468_);
lean_dec_ref(v_a_6467_);
lean_dec(v_a_6466_);
lean_dec_ref(v_a_6465_);
lean_dec(v_a_6464_);
lean_dec_ref(v_a_6463_);
return v_res_6472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6473_, lean_object* v_msg_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_){
_start:
{
lean_object* v___x_6484_; 
v___x_6484_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6474_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
return v___x_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6485_, lean_object* v_msg_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_){
_start:
{
lean_object* v_res_6496_; 
v_res_6496_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6485_, v_msg_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_);
lean_dec(v___y_6494_);
lean_dec_ref(v___y_6493_);
lean_dec(v___y_6492_);
lean_dec_ref(v___y_6491_);
lean_dec(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec(v___y_6488_);
lean_dec_ref(v___y_6487_);
return v_res_6496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6502_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6505_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6506_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6502_, v___x_6503_, v___x_6504_, v___x_6505_);
return v___x_6506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6507_){
_start:
{
lean_object* v_res_6508_; 
v_res_6508_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6509_, lean_object* v_ty_x3f_6510_, lean_object* v_a_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_){
_start:
{
lean_object* v___x_6521_; 
v___x_6521_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6509_, v_ty_x3f_6510_, v_a_6511_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_);
if (lean_obj_tag(v___x_6521_) == 0)
{
lean_object* v_a_6522_; lean_object* v___x_6523_; 
v_a_6522_ = lean_ctor_get(v___x_6521_, 0);
lean_inc(v_a_6522_);
lean_dec_ref_known(v___x_6521_, 1);
v___x_6523_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6522_, v___y_6513_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_);
return v___x_6523_;
}
else
{
lean_object* v_a_6524_; lean_object* v___x_6526_; uint8_t v_isShared_6527_; uint8_t v_isSharedCheck_6531_; 
v_a_6524_ = lean_ctor_get(v___x_6521_, 0);
v_isSharedCheck_6531_ = !lean_is_exclusive(v___x_6521_);
if (v_isSharedCheck_6531_ == 0)
{
v___x_6526_ = v___x_6521_;
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
else
{
lean_inc(v_a_6524_);
lean_dec(v___x_6521_);
v___x_6526_ = lean_box(0);
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
v_resetjp_6525_:
{
lean_object* v___x_6529_; 
if (v_isShared_6527_ == 0)
{
v___x_6529_ = v___x_6526_;
goto v_reusejp_6528_;
}
else
{
lean_object* v_reuseFailAlloc_6530_; 
v_reuseFailAlloc_6530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_a_6524_);
v___x_6529_ = v_reuseFailAlloc_6530_;
goto v_reusejp_6528_;
}
v_reusejp_6528_:
{
return v___x_6529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6532_, lean_object* v_ty_x3f_6533_, lean_object* v_a_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_){
_start:
{
lean_object* v_res_6544_; 
v_res_6544_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6532_, v_ty_x3f_6533_, v_a_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_);
lean_dec(v___y_6542_);
lean_dec_ref(v___y_6541_);
lean_dec(v___y_6540_);
lean_dec_ref(v___y_6539_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6535_);
return v_res_6544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6551_, lean_object* v_a_6552_, lean_object* v_a_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_, lean_object* v_a_6556_, lean_object* v_a_6557_, lean_object* v_a_6558_, lean_object* v_a_6559_){
_start:
{
lean_object* v___x_6561_; uint8_t v___x_6562_; 
v___x_6561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6551_);
v___x_6562_ = l_Lean_Syntax_isOfKind(v_stx_6551_, v___x_6561_);
if (v___x_6562_ == 0)
{
lean_object* v___x_6563_; 
lean_dec(v_stx_6551_);
v___x_6563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6563_;
}
else
{
lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v_ty_x3f_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; lean_object* v___y_6573_; lean_object* v___y_6574_; lean_object* v___y_6575_; lean_object* v___x_6589_; lean_object* v___x_6590_; uint8_t v___x_6591_; 
v___x_6564_ = lean_unsigned_to_nat(1u);
v___x_6565_ = l_Lean_Syntax_getArg(v_stx_6551_, v___x_6564_);
v___x_6589_ = lean_unsigned_to_nat(2u);
v___x_6590_ = l_Lean_Syntax_getArg(v_stx_6551_, v___x_6589_);
lean_dec(v_stx_6551_);
v___x_6591_ = l_Lean_Syntax_isNone(v___x_6590_);
if (v___x_6591_ == 0)
{
uint8_t v___x_6592_; 
lean_inc(v___x_6590_);
v___x_6592_ = l_Lean_Syntax_matchesNull(v___x_6590_, v___x_6589_);
if (v___x_6592_ == 0)
{
lean_object* v___x_6593_; 
lean_dec(v___x_6590_);
lean_dec(v___x_6565_);
v___x_6593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6593_;
}
else
{
lean_object* v_ty_x3f_6594_; lean_object* v___x_6595_; 
v_ty_x3f_6594_ = l_Lean_Syntax_getArg(v___x_6590_, v___x_6564_);
lean_dec(v___x_6590_);
v___x_6595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6595_, 0, v_ty_x3f_6594_);
v_ty_x3f_6567_ = v___x_6595_;
v___y_6568_ = v_a_6552_;
v___y_6569_ = v_a_6553_;
v___y_6570_ = v_a_6554_;
v___y_6571_ = v_a_6555_;
v___y_6572_ = v_a_6556_;
v___y_6573_ = v_a_6557_;
v___y_6574_ = v_a_6558_;
v___y_6575_ = v_a_6559_;
goto v___jp_6566_;
}
}
else
{
lean_object* v___x_6596_; 
lean_dec(v___x_6590_);
v___x_6596_ = lean_box(0);
v_ty_x3f_6567_ = v___x_6596_;
v___y_6568_ = v_a_6552_;
v___y_6569_ = v_a_6553_;
v___y_6570_ = v_a_6554_;
v___y_6571_ = v_a_6555_;
v___y_6572_ = v_a_6556_;
v___y_6573_ = v_a_6557_;
v___y_6574_ = v_a_6558_;
v___y_6575_ = v_a_6559_;
goto v___jp_6566_;
}
v___jp_6566_:
{
lean_object* v_pats_6576_; lean_object* v___x_6577_; 
v_pats_6576_ = l_Lean_Syntax_getArgs(v___x_6565_);
lean_dec(v___x_6565_);
v___x_6577_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6569_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; lean_object* v___f_6579_; lean_object* v___x_6580_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
lean_inc_n(v_a_6578_, 2);
lean_dec_ref_known(v___x_6577_, 1);
v___f_6579_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6579_, 0, v_pats_6576_);
lean_closure_set(v___f_6579_, 1, v_ty_x3f_6567_);
lean_closure_set(v___f_6579_, 2, v_a_6578_);
v___x_6580_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6578_, v___f_6579_, v___y_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_);
return v___x_6580_;
}
else
{
lean_object* v_a_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6588_; 
lean_dec_ref(v_pats_6576_);
lean_dec(v_ty_x3f_6567_);
v_a_6581_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6583_ = v___x_6577_;
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_a_6581_);
lean_dec(v___x_6577_);
v___x_6583_ = lean_box(0);
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
v_resetjp_6582_:
{
lean_object* v___x_6586_; 
if (v_isShared_6584_ == 0)
{
v___x_6586_ = v___x_6583_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_a_6581_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_, lean_object* v_a_6606_){
_start:
{
lean_object* v_res_6607_; 
v_res_6607_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6597_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_, v_a_6602_, v_a_6603_, v_a_6604_, v_a_6605_);
lean_dec(v_a_6605_);
lean_dec_ref(v_a_6604_);
lean_dec(v_a_6603_);
lean_dec_ref(v_a_6602_);
lean_dec(v_a_6601_);
lean_dec_ref(v_a_6600_);
lean_dec(v_a_6599_);
lean_dec_ref(v_a_6598_);
return v_res_6607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; 
v___x_6613_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6616_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6617_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6613_, v___x_6614_, v___x_6615_, v___x_6616_);
return v___x_6617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6618_){
_start:
{
lean_object* v_res_6619_; 
v_res_6619_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6619_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Induction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_RCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_initFn_00___x40_Lean_Elab_Tactic_RCases_1136698826____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_RCases_linter_unusedRCasesPattern = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_RCases_linter_unusedRCasesPattern);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_RCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Induction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_RCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_RCases(builtin);
}
#ifdef __cplusplus
}
#endif
