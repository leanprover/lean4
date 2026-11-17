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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_append(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___lam__0(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___impl(lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_tag_nat(v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___impl___boxed(lean_object* v_x_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorIdx___impl(v_x_131_);
lean_dec_ref(v_x_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(lean_object* v_t_133_, lean_object* v_k_134_){
_start:
{
switch(lean_obj_tag(v_t_133_))
{
case 0:
{
lean_object* v_ref_135_; lean_object* v_a_136_; lean_object* v___x_137_; 
v_ref_135_ = lean_ctor_get(v_t_133_, 0);
lean_inc(v_ref_135_);
v_a_136_ = lean_ctor_get(v_t_133_, 1);
lean_inc_ref(v_a_136_);
lean_dec_ref_known(v_t_133_, 2);
v___x_137_ = lean_apply_2(v_k_134_, v_ref_135_, v_a_136_);
return v___x_137_;
}
case 2:
{
lean_object* v_ref_138_; lean_object* v___x_139_; 
v_ref_138_ = lean_ctor_get(v_t_133_, 0);
lean_inc(v_ref_138_);
lean_dec_ref_known(v_t_133_, 1);
v___x_139_ = lean_apply_1(v_k_134_, v_ref_138_);
return v___x_139_;
}
case 3:
{
lean_object* v_ref_140_; lean_object* v_a_141_; lean_object* v___x_142_; 
v_ref_140_ = lean_ctor_get(v_t_133_, 0);
lean_inc(v_ref_140_);
v_a_141_ = lean_ctor_get(v_t_133_, 1);
lean_inc_ref(v_a_141_);
lean_dec_ref_known(v_t_133_, 2);
v___x_142_ = lean_apply_2(v_k_134_, v_ref_140_, v_a_141_);
return v___x_142_;
}
case 4:
{
lean_object* v_ref_143_; lean_object* v_a_144_; lean_object* v_a_145_; lean_object* v___x_146_; 
v_ref_143_ = lean_ctor_get(v_t_133_, 0);
lean_inc(v_ref_143_);
v_a_144_ = lean_ctor_get(v_t_133_, 1);
lean_inc_ref(v_a_144_);
v_a_145_ = lean_ctor_get(v_t_133_, 2);
lean_inc(v_a_145_);
lean_dec_ref_known(v_t_133_, 3);
v___x_146_ = lean_apply_3(v_k_134_, v_ref_143_, v_a_144_, v_a_145_);
return v___x_146_;
}
default: 
{
lean_object* v_ref_147_; lean_object* v_a_148_; lean_object* v___x_149_; 
v_ref_147_ = lean_ctor_get(v_t_133_, 0);
lean_inc(v_ref_147_);
v_a_148_ = lean_ctor_get(v_t_133_, 1);
lean_inc(v_a_148_);
lean_dec_ref(v_t_133_);
v___x_149_ = lean_apply_2(v_k_134_, v_ref_147_, v_a_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim(lean_object* v_motive__1_150_, lean_object* v_ctorIdx_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_k_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_152_, v_k_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___boxed(lean_object* v_motive__1_156_, lean_object* v_ctorIdx_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_k_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim(v_motive__1_156_, v_ctorIdx_157_, v_t_158_, v_h_159_, v_k_160_);
lean_dec(v_ctorIdx_157_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim___redArg(lean_object* v_t_162_, lean_object* v_paren_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_162_, v_paren_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_paren_elim(lean_object* v_motive__1_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_paren_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_166_, v_paren_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim___redArg(lean_object* v_t_170_, lean_object* v_one_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_170_, v_one_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_one_elim(lean_object* v_motive__1_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_one_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_174_, v_one_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim___redArg(lean_object* v_t_178_, lean_object* v_clear_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_178_, v_clear_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_clear_elim(lean_object* v_motive__1_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_clear_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_182_, v_clear_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim___redArg(lean_object* v_t_186_, lean_object* v_explicit_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_186_, v_explicit_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_explicit_elim(lean_object* v_motive__1_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_explicit_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_190_, v_explicit_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim___redArg(lean_object* v_t_194_, lean_object* v_typed_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_194_, v_typed_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_typed_elim(lean_object* v_motive__1_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_typed_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_198_, v_typed_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim___redArg(lean_object* v_t_202_, lean_object* v_tuple_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_202_, v_tuple_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_tuple_elim(lean_object* v_motive__1_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_tuple_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_206_, v_tuple_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim___redArg(lean_object* v_t_210_, lean_object* v_alts_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_210_, v_alts_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_RCasesPatt_alts_elim(lean_object* v_motive__1_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_alts_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Elab_Tactic_RCases_RCasesPatt_ctorElim___redArg(v_t_214_, v_alts_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(2u);
v___x_225_ = lean_nat_to_int(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_to_int(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_dec(v_x_267_);
return v_x_268_;
}
else
{
lean_object* v_head_270_; lean_object* v_tail_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
v_head_270_ = lean_ctor_get(v_x_269_, 0);
v_tail_271_ = lean_ctor_get(v_x_269_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_282_ == 0)
{
v___x_273_ = v_x_269_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tail_271_);
lean_inc(v_head_270_);
lean_dec(v_x_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
lean_inc(v_x_267_);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 5);
lean_ctor_set(v___x_273_, 1, v_x_267_);
lean_ctor_set(v___x_273_, 0, v_x_268_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_x_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_x_267_);
v___x_276_ = v_reuseFailAlloc_281_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_head_270_, v___x_277_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v_x_268_ = v___x_279_;
v_x_269_ = v_tail_271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_dec(v_x_283_);
return v_x_284_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
v_head_286_ = lean_ctor_get(v_x_285_, 0);
v_tail_287_ = lean_ctor_get(v_x_285_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_298_ == 0)
{
v___x_289_ = v_x_285_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_tail_287_);
lean_inc(v_head_286_);
lean_dec(v_x_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
lean_inc(v_x_283_);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 5);
lean_ctor_set(v___x_289_, 1, v_x_283_);
lean_ctor_set(v___x_289_, 0, v_x_284_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_x_284_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_x_283_);
v___x_292_ = v_reuseFailAlloc_297_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_head_286_, v___x_293_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1_spec__3(v_x_283_, v___x_295_, v_tail_287_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v___x_301_; 
lean_dec(v_x_300_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_tail_302_; 
v_tail_302_ = lean_ctor_get(v_x_299_, 1);
if (lean_obj_tag(v_tail_302_) == 0)
{
lean_object* v_head_303_; lean_object* v___x_304_; 
lean_dec(v_x_300_);
v_head_303_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_head_303_);
lean_dec_ref_known(v_x_299_, 2);
v___x_304_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(v_head_303_);
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_inc(v_tail_302_);
v_head_305_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_head_305_);
lean_dec_ref_known(v_x_299_, 2);
v___x_306_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(v_head_305_);
v___x_307_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0_spec__1(v_x_300_, v___x_306_, v_tail_302_);
return v___x_307_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__2));
v___x_310_ = lean_string_length(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__7);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(lean_object* v_a_318_){
_start:
{
if (lean_obj_tag(v_a_318_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__1));
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; 
v___x_320_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__5));
v___x_321_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0(v_a_318_, v___x_320_);
v___x_322_ = lean_obj_once(&l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__8);
v___x_323_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__9));
v___x_324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_321_);
v___x_325_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__10));
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_322_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = 0;
v___x_329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*1, v___x_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(lean_object* v_x_336_, lean_object* v_prec_337_){
_start:
{
switch(lean_obj_tag(v_x_336_))
{
case 0:
{
lean_object* v_ref_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_362_; 
v_ref_338_ = lean_ctor_get(v_x_336_, 0);
v_a_339_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_362_ == 0)
{
v___x_341_ = v_x_336_;
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_inc(v_ref_338_);
lean_dec(v_x_336_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___y_345_; uint8_t v___x_359_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_359_ = lean_nat_dec_le(v___x_343_, v_prec_337_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_345_ = v___x_360_;
goto v___jp_344_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_345_ = v___x_361_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_346_ = lean_box(1);
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__2));
v___x_348_ = l_Lean_Syntax_instRepr_repr(v_ref_338_, v___x_343_);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 5);
lean_ctor_set(v___x_341_, 1, v___x_348_);
lean_ctor_set(v___x_341_, 0, v___x_347_);
v___x_350_ = v___x_341_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_358_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_346_);
v___x_352_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_339_, v___x_343_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
lean_inc(v___y_345_);
v___x_354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_345_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = 0;
v___x_356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*1, v___x_355_);
v___x_357_ = l_Repr_addAppParen(v___x_356_, v_prec_337_);
return v___x_357_;
}
}
}
}
case 1:
{
lean_object* v_ref_363_; lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_388_; 
v_ref_363_ = lean_ctor_get(v_x_336_, 0);
v_a_364_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_388_ == 0)
{
v___x_366_ = v_x_336_;
v_isShared_367_ = v_isSharedCheck_388_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_inc(v_ref_363_);
lean_dec(v_x_336_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_388_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___y_369_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1024u);
v___x_385_ = lean_nat_dec_le(v___x_384_, v_prec_337_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_369_ = v___x_386_;
goto v___jp_368_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_369_ = v___x_387_;
goto v___jp_368_;
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_370_ = lean_box(1);
v___x_371_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__7));
v___x_372_ = lean_unsigned_to_nat(1024u);
v___x_373_ = l_Lean_Syntax_instRepr_repr(v_ref_363_, v___x_372_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 5);
lean_ctor_set(v___x_366_, 1, v___x_373_);
lean_ctor_set(v___x_366_, 0, v___x_371_);
v___x_375_ = v___x_366_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_370_);
v___x_377_ = l_Lean_Name_reprPrec(v_a_364_, v___x_372_);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_inc(v___y_369_);
v___x_379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_379_, 0, v___y_369_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = 0;
v___x_381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
v___x_382_ = l_Repr_addAppParen(v___x_381_, v_prec_337_);
return v___x_382_;
}
}
}
}
case 2:
{
lean_object* v_ref_389_; lean_object* v___y_391_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_ref_389_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_ref_389_);
lean_dec_ref_known(v_x_336_, 1);
v___x_400_ = lean_unsigned_to_nat(1024u);
v___x_401_ = lean_nat_dec_le(v___x_400_, v_prec_337_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_391_ = v___x_402_;
goto v___jp_390_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_391_ = v___x_403_;
goto v___jp_390_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_392_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__10));
v___x_393_ = lean_unsigned_to_nat(1024u);
v___x_394_ = l_Lean_Syntax_instRepr_repr(v_ref_389_, v___x_393_);
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_392_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_inc(v___y_391_);
v___x_396_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_396_, 0, v___y_391_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = 0;
v___x_398_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*1, v___x_397_);
v___x_399_ = l_Repr_addAppParen(v___x_398_, v_prec_337_);
return v___x_399_;
}
}
case 3:
{
lean_object* v_ref_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_428_; 
v_ref_404_ = lean_ctor_get(v_x_336_, 0);
v_a_405_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_428_ == 0)
{
v___x_407_ = v_x_336_;
v_isShared_408_ = v_isSharedCheck_428_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_inc(v_ref_404_);
lean_dec(v_x_336_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_428_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___y_411_; uint8_t v___x_425_; 
v___x_409_ = lean_unsigned_to_nat(1024u);
v___x_425_ = lean_nat_dec_le(v___x_409_, v_prec_337_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_411_ = v___x_426_;
goto v___jp_410_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_411_ = v___x_427_;
goto v___jp_410_;
}
v___jp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_412_ = lean_box(1);
v___x_413_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__13));
v___x_414_ = l_Lean_Syntax_instRepr_repr(v_ref_404_, v___x_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 5);
lean_ctor_set(v___x_407_, 1, v___x_414_);
lean_ctor_set(v___x_407_, 0, v___x_413_);
v___x_416_ = v___x_407_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_414_);
v___x_416_ = v_reuseFailAlloc_424_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_412_);
v___x_418_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_405_, v___x_409_);
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
lean_inc(v___y_411_);
v___x_420_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_420_, 0, v___y_411_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = 0;
v___x_422_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1, v___x_421_);
v___x_423_ = l_Repr_addAppParen(v___x_422_, v_prec_337_);
return v___x_423_;
}
}
}
}
case 4:
{
lean_object* v_ref_429_; lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_432_; lean_object* v___y_434_; uint8_t v___x_449_; 
v_ref_429_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_ref_429_);
v_a_430_ = lean_ctor_get(v_x_336_, 1);
lean_inc_ref(v_a_430_);
v_a_431_ = lean_ctor_get(v_x_336_, 2);
lean_inc(v_a_431_);
lean_dec_ref_known(v_x_336_, 3);
v___x_432_ = lean_unsigned_to_nat(1024u);
v___x_449_ = lean_nat_dec_le(v___x_432_, v_prec_337_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_434_ = v___x_450_;
goto v___jp_433_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_434_ = v___x_451_;
goto v___jp_433_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_435_ = lean_box(1);
v___x_436_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__16));
v___x_437_ = l_Lean_Syntax_instRepr_repr(v_ref_429_, v___x_432_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_435_);
v___x_440_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_a_430_, v___x_432_);
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_435_);
v___x_443_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_a_431_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_inc(v___y_434_);
v___x_445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_445_, 0, v___y_434_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = 0;
v___x_447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1, v___x_446_);
v___x_448_ = l_Repr_addAppParen(v___x_447_, v_prec_337_);
return v___x_448_;
}
}
case 5:
{
lean_object* v_ref_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_477_; 
v_ref_452_ = lean_ctor_get(v_x_336_, 0);
v_a_453_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_477_ == 0)
{
v___x_455_ = v_x_336_;
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_inc(v_ref_452_);
lean_dec(v_x_336_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___y_458_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(1024u);
v___x_474_ = lean_nat_dec_le(v___x_473_, v_prec_337_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_458_ = v___x_475_;
goto v___jp_457_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_458_ = v___x_476_;
goto v___jp_457_;
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_459_ = lean_box(1);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__19));
v___x_461_ = lean_unsigned_to_nat(1024u);
v___x_462_ = l_Lean_Syntax_instRepr_repr(v_ref_452_, v___x_461_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_462_);
lean_ctor_set(v___x_455_, 0, v___x_460_);
v___x_464_ = v___x_455_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_472_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_459_);
v___x_466_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_453_);
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_inc(v___y_458_);
v___x_468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_468_, 0, v___y_458_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = 0;
v___x_470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1, v___x_469_);
v___x_471_ = l_Repr_addAppParen(v___x_470_, v_prec_337_);
return v___x_471_;
}
}
}
}
default: 
{
lean_object* v_ref_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_503_; 
v_ref_478_ = lean_ctor_get(v_x_336_, 0);
v_a_479_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_503_ == 0)
{
v___x_481_ = v_x_336_;
v_isShared_482_ = v_isSharedCheck_503_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_inc(v_ref_478_);
lean_dec(v_x_336_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_503_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___y_484_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1024u);
v___x_500_ = lean_nat_dec_le(v___x_499_, v_prec_337_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__3);
v___y_484_ = v___x_501_;
goto v___jp_483_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4, &l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4_once, _init_l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__4);
v___y_484_ = v___x_502_;
goto v___jp_483_;
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_485_ = lean_box(1);
v___x_486_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___closed__22));
v___x_487_ = lean_unsigned_to_nat(1024u);
v___x_488_ = l_Lean_Syntax_instRepr_repr(v_ref_478_, v___x_487_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 5);
lean_ctor_set(v___x_481_, 1, v___x_488_);
lean_ctor_set(v___x_481_, 0, v___x_486_);
v___x_490_ = v___x_481_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_498_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_485_);
v___x_492_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_479_);
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
lean_inc(v___y_484_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_484_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
v___x_497_ = l_Repr_addAppParen(v___x_496_, v_prec_337_);
return v___x_497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__0___lam__0(lean_object* v___y_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v___y_504_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr___boxed(lean_object* v_x_507_, lean_object* v_prec_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr(v_x_507_, v_prec_508_);
lean_dec(v_prec_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0_spec__1(lean_object* v_a_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_nat_to_int(v_a_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0(lean_object* v_a_512_, lean_object* v_n_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg(v_a_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___boxed(lean_object* v_a_515_, lean_object* v_n_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0(v_a_515_, v_n_516_);
lean_dec(v_n_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(lean_object* v_x_528_){
_start:
{
switch(lean_obj_tag(v_x_528_))
{
case 1:
{
lean_object* v_a_529_; 
v_a_529_ = lean_ctor_get(v_x_528_, 1);
if (lean_obj_tag(v_a_529_) == 1)
{
lean_object* v_pre_530_; 
v_pre_530_ = lean_ctor_get(v_a_529_, 0);
if (lean_obj_tag(v_pre_530_) == 0)
{
lean_object* v_str_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_str_531_ = lean_ctor_get(v_a_529_, 1);
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__0));
v___x_533_ = lean_string_dec_eq(v_str_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_535_ = lean_string_dec_eq(v_str_531_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_inc_ref(v_a_529_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_a_529_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
else
{
lean_object* v___x_539_; 
lean_inc_ref(v_a_529_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_a_529_);
return v___x_539_;
}
}
else
{
lean_object* v___x_540_; 
lean_inc(v_a_529_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_a_529_);
return v___x_540_;
}
}
case 0:
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v_x_528_, 1);
v_x_528_ = v_a_541_;
goto _start;
}
case 4:
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v_x_528_, 1);
v_x_528_ = v_a_543_;
goto _start;
}
case 6:
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v_x_528_, 1);
if (lean_obj_tag(v_a_545_) == 1)
{
lean_object* v_tail_546_; 
v_tail_546_ = lean_ctor_get(v_a_545_, 1);
if (lean_obj_tag(v_tail_546_) == 0)
{
lean_object* v_head_547_; 
v_head_547_ = lean_ctor_get(v_a_545_, 0);
v_x_528_ = v_head_547_;
goto _start;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(0);
return v___x_550_;
}
}
default: 
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(0);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___boxed(lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_x_552_);
lean_dec_ref(v_x_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref(lean_object* v_x_554_){
_start:
{
lean_object* v_ref_555_; 
v_ref_555_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_ref_555_);
return v_ref_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref___boxed(lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_ref(v_x_556_);
lean_dec_ref(v_x_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(lean_object* v_x_558_){
_start:
{
switch(lean_obj_tag(v_x_558_))
{
case 0:
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v_x_558_, 1);
lean_inc_ref(v_a_559_);
lean_dec_ref_known(v_x_558_, 2);
v_x_558_ = v_a_559_;
goto _start;
}
case 3:
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_a_561_ = lean_ctor_get(v_x_558_, 1);
lean_inc_ref(v_a_561_);
lean_dec_ref_known(v_x_558_, 2);
v___x_562_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_a_561_);
v_snd_563_ = lean_ctor_get(v___x_562_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_562_, 0);
lean_dec(v_unused_573_);
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = 1;
v___x_568_ = lean_box(v___x_567_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_563_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
case 5:
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_583_; 
v_a_574_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v_x_558_, 0);
lean_dec(v_unused_584_);
v___x_576_ = v_x_558_;
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v_x_558_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = 0;
v___x_579_ = lean_box(v___x_578_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_579_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_574_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
default: 
{
uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_585_ = 0;
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v_x_558_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_box(v___x_585_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(lean_object* v_x_590_){
_start:
{
switch(lean_obj_tag(v_x_590_))
{
case 0:
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v_x_590_, 1);
lean_inc_ref(v_a_591_);
lean_dec_ref_known(v_x_590_, 2);
v_x_590_ = v_a_591_;
goto _start;
}
case 6:
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v_x_590_, 1);
lean_inc(v_a_593_);
lean_dec_ref_known(v_x_590_, 2);
return v_a_593_;
}
default: 
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v_x_590_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(lean_object* v_ref_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_dec(v_ref_596_);
return v_x_597_;
}
else
{
lean_object* v_val_599_; lean_object* v___x_600_; 
v_val_599_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_val_599_);
v___x_600_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_600_, 0, v_ref_596_);
lean_ctor_set(v___x_600_, 1, v_x_597_);
lean_ctor_set(v___x_600_, 2, v_val_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f___boxed(lean_object* v_ref_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_601_, v_x_602_, v_x_603_);
lean_dec(v_x_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_x27(lean_object* v_x_605_){
_start:
{
lean_object* v_ps_607_; 
if (lean_obj_tag(v_x_605_) == 1)
{
lean_object* v_tail_634_; 
v_tail_634_ = lean_ctor_get(v_x_605_, 1);
if (lean_obj_tag(v_tail_634_) == 0)
{
lean_object* v_head_635_; 
v_head_635_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_head_635_);
lean_dec_ref_known(v_x_605_, 2);
return v_head_635_;
}
else
{
v_ps_607_ = v_x_605_;
goto v___jp_606_;
}
}
else
{
v_ps_607_ = v_x_605_;
goto v___jp_606_;
}
v___jp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = l_List_head_x3f___redArg(v_ps_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_ps_607_);
return v___x_610_;
}
else
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_608_, 1);
switch(lean_obj_tag(v_val_611_))
{
case 2:
{
lean_object* v_ref_612_; lean_object* v___x_613_; 
v_ref_612_ = lean_ctor_get(v_val_611_, 0);
lean_inc(v_ref_612_);
lean_dec_ref_known(v_val_611_, 1);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v_ref_612_);
lean_ctor_set(v___x_613_, 1, v_ps_607_);
return v___x_613_;
}
case 4:
{
lean_object* v_ref_614_; lean_object* v___x_615_; 
v_ref_614_ = lean_ctor_get(v_val_611_, 0);
lean_inc(v_ref_614_);
lean_dec_ref_known(v_val_611_, 3);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v_ref_614_);
lean_ctor_set(v___x_615_, 1, v_ps_607_);
return v___x_615_;
}
case 5:
{
lean_object* v_ref_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_ref_616_ = lean_ctor_get(v_val_611_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_val_611_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_val_611_, 1);
lean_dec(v_unused_624_);
v___x_618_ = v_val_611_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_ref_616_);
lean_dec(v_val_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_ps_607_);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_ref_616_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_ps_607_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
default: 
{
lean_object* v_ref_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_ref_625_ = lean_ctor_get(v_val_611_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_val_611_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_val_611_, 1);
lean_dec(v_unused_633_);
v___x_627_ = v_val_611_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_ref_625_);
lean_dec(v_val_611_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 5);
lean_ctor_set(v___x_627_, 1, v_ps_607_);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_ref_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_ps_607_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(lean_object* v_ref_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 1)
{
lean_object* v_tail_638_; 
v_tail_638_ = lean_ctor_get(v_x_637_, 1);
if (lean_obj_tag(v_tail_638_) == 0)
{
lean_object* v_head_639_; 
lean_dec(v_ref_636_);
v_head_639_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_head_639_);
lean_dec_ref_known(v_x_637_, 2);
return v_head_639_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_640_, 0, v_ref_636_);
lean_ctor_set(v___x_640_, 1, v_x_637_);
return v___x_640_;
}
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_641_, 0, v_ref_636_);
lean_ctor_set(v___x_641_, 1, v_x_637_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
return v_x_642_;
}
else
{
lean_object* v_head_643_; lean_object* v_tail_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_664_; 
v_head_643_ = lean_ctor_get(v_x_642_, 0);
v_tail_644_ = lean_ctor_get(v_x_642_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_664_ == 0)
{
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_tail_644_);
lean_inc(v_head_643_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
if (lean_obj_tag(v_head_643_) == 5)
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v_head_643_, 1);
if (lean_obj_tag(v_a_653_) == 0)
{
if (lean_obj_tag(v_tail_644_) == 0)
{
lean_object* v_ref_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_646_);
v_ref_654_ = lean_ctor_get(v_head_643_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_head_643_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_head_643_, 1);
lean_dec(v_unused_663_);
v___x_656_ = v_head_643_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_ref_654_);
lean_dec(v_head_643_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v_tail_644_);
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_ref_654_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_tail_644_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_tail_644_);
return v___x_660_;
}
}
}
else
{
goto v___jp_648_;
}
}
else
{
if (lean_obj_tag(v_tail_644_) == 0)
{
lean_inc(v_a_653_);
lean_dec_ref_known(v_head_643_, 2);
lean_del_object(v___x_646_);
return v_a_653_;
}
else
{
goto v___jp_648_;
}
}
}
else
{
goto v___jp_648_;
}
v___jp_648_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(v_tail_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_head_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081(lean_object* v_x_665_){
_start:
{
lean_object* v___y_667_; lean_object* v___y_668_; 
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
return v___x_671_;
}
else
{
lean_object* v_head_672_; lean_object* v_tail_673_; lean_object* v___x_674_; lean_object* v_ps_676_; 
v_head_672_ = lean_ctor_get(v_x_665_, 0);
v_tail_673_ = lean_ctor_get(v_x_665_, 1);
v___x_674_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited));
if (lean_obj_tag(v_head_672_) == 1)
{
if (lean_obj_tag(v_tail_673_) == 0)
{
lean_inc_ref(v_head_672_);
lean_dec_ref_known(v_x_665_, 2);
return v_head_672_;
}
else
{
v_ps_676_ = v_x_665_;
goto v___jp_675_;
}
}
else
{
v_ps_676_ = v_x_665_;
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v_ref_678_; 
v___x_677_ = l_List_head_x21___redArg(v___x_674_, v_ps_676_);
v_ref_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_ref_678_);
lean_dec(v___x_677_);
v___y_667_ = v_ps_676_;
v___y_668_ = v_ref_678_;
goto v___jp_666_;
}
}
v___jp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081Core(v___y_667_);
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_object* v___x_680_; 
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v_head_681_; lean_object* v_tail_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_695_; 
v_head_681_ = lean_ctor_get(v_x_679_, 0);
v_tail_682_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_695_ == 0)
{
v___x_684_ = v_x_679_;
v_isShared_685_ = v_isSharedCheck_695_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_tail_682_);
lean_inc(v_head_681_);
lean_dec(v_x_679_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_695_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
if (lean_obj_tag(v_head_681_) == 1)
{
lean_object* v_head_692_; 
v_head_692_ = lean_ctor_get(v_head_681_, 0);
if (lean_obj_tag(v_head_692_) == 6)
{
lean_object* v_tail_693_; 
v_tail_693_ = lean_ctor_get(v_head_681_, 1);
if (lean_obj_tag(v_tail_693_) == 0)
{
if (lean_obj_tag(v_tail_682_) == 0)
{
lean_object* v_a_694_; 
lean_inc_ref(v_head_692_);
lean_dec_ref_known(v_head_681_, 2);
lean_del_object(v___x_684_);
v_a_694_ = lean_ctor_get(v_head_692_, 1);
lean_inc(v_a_694_);
lean_dec_ref_known(v_head_692_, 2);
return v_a_694_;
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_686_;
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_687_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_tuple_u2081(v_head_681_);
v___x_688_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(v_tail_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_688_);
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081(lean_object* v_ref_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_ps_699_; 
if (lean_obj_tag(v_x_697_) == 1)
{
lean_object* v_head_702_; 
v_head_702_ = lean_ctor_get(v_x_697_, 0);
if (lean_obj_tag(v_head_702_) == 0)
{
lean_object* v_tail_703_; 
v_tail_703_ = lean_ctor_get(v_x_697_, 1);
if (lean_obj_tag(v_tail_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_head_702_);
lean_dec(v_ref_696_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_697_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_x_697_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_x_697_, 0);
lean_dec(v_unused_713_);
v___x_705_ = v_x_697_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_x_697_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 5);
lean_ctor_set(v___x_705_, 1, v_head_702_);
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_head_702_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
v_ps_699_ = v_x_697_;
goto v___jp_698_;
}
}
else
{
lean_object* v_head_714_; 
v_head_714_ = lean_ctor_get(v_head_702_, 0);
lean_inc(v_head_714_);
if (lean_obj_tag(v_head_714_) == 6)
{
lean_object* v_tail_715_; 
v_tail_715_ = lean_ctor_get(v_head_702_, 1);
if (lean_obj_tag(v_tail_715_) == 0)
{
lean_object* v_tail_716_; 
v_tail_716_ = lean_ctor_get(v_x_697_, 1);
if (lean_obj_tag(v_tail_716_) == 0)
{
lean_object* v_ref_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref_known(v_x_697_, 2);
lean_dec(v_ref_696_);
v_ref_717_ = lean_ctor_get(v_head_714_, 0);
v_a_718_ = lean_ctor_get(v_head_714_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_head_714_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v_head_714_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_inc(v_ref_717_);
lean_dec(v_head_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 5);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_ref_717_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_dec_ref_known(v_head_714_, 2);
v_ps_699_ = v_x_697_;
goto v___jp_698_;
}
}
else
{
lean_dec_ref_known(v_head_714_, 2);
v_ps_699_ = v_x_697_;
goto v___jp_698_;
}
}
else
{
lean_dec(v_head_714_);
v_ps_699_ = v_x_697_;
goto v___jp_698_;
}
}
}
else
{
v_ps_699_ = v_x_697_;
goto v___jp_698_;
}
v___jp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_u2081Core(v_ps_699_);
v___x_701_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_ref_696_, v___x_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(lean_object* v_tgt_726_, lean_object* v_p_727_, lean_object* v_m_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_lt(v_tgt_726_, v_p_727_);
if (v___x_729_ == 0)
{
return v_m_728_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_MessageData_paren(v_m_728_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove___boxed(lean_object* v_tgt_731_, lean_object* v_p_732_, lean_object* v_m_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v_tgt_731_, v_p_732_, v_m_733_);
lean_dec(v_p_732_);
lean_dec(v_tgt_731_);
return v_res_734_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__1));
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__3));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__5));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_box(1);
v___x_748_ = l_Lean_MessageData_ofFormat(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_List_repr___at___00Lean_Elab_Tactic_RCases_instReprRCasesPatt_repr_spec__0___redArg___closed__4));
v___x_750_ = l_Lean_MessageData_ofFormat(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
v___x_752_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__8);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__1(lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
if (lean_obj_tag(v_a_755_) == 0)
{
lean_object* v___x_757_; 
v___x_757_ = l_List_reverse___redArg(v_a_756_);
return v___x_757_;
}
else
{
lean_object* v_head_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_769_; 
v_head_758_ = lean_ctor_get(v_a_755_, 0);
v_tail_759_ = lean_ctor_get(v_a_755_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_769_ == 0)
{
v___x_761_ = v_a_755_;
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_head_758_);
lean_dec(v_a_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_763_, v_head_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_a_756_);
lean_ctor_set(v___x_761_, 0, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_756_);
v___x_766_ = v_reuseFailAlloc_768_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v_a_755_ = v_tail_759_;
v_a_756_ = v___x_766_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__13));
v___x_774_ = l_Lean_MessageData_ofFormat(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
switch(lean_obj_tag(v_a_776_))
{
case 0:
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v_a_776_, 1);
lean_inc_ref(v_a_777_);
lean_dec_ref_known(v_a_776_, 2);
v_a_776_ = v_a_777_;
goto _start;
}
case 1:
{
lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_779_ = lean_ctor_get(v_a_776_, 1);
lean_inc(v_a_779_);
lean_dec_ref_known(v_a_776_, 2);
v___x_780_ = l_Lean_MessageData_ofName(v_a_779_);
return v___x_780_;
}
case 2:
{
lean_object* v___x_781_; 
lean_dec_ref_known(v_a_776_, 1);
v___x_781_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__2);
return v___x_781_;
}
case 3:
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_792_; 
v_a_782_ = lean_ctor_get(v_a_776_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_a_776_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_a_776_, 0);
lean_dec(v_unused_793_);
v___x_784_ = v_a_776_;
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v_a_776_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_786_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__4);
v___x_787_ = lean_unsigned_to_nat(2u);
v___x_788_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_787_, v_a_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 7);
lean_ctor_set(v___x_784_, 1, v___x_788_);
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
case 4:
{
lean_object* v_a_794_; lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_a_794_ = lean_ctor_get(v_a_776_, 1);
lean_inc_ref(v_a_794_);
v_a_795_ = lean_ctor_get(v_a_776_, 2);
lean_inc(v_a_795_);
lean_dec_ref_known(v_a_776_, 3);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_797_, v_a_794_);
v___x_799_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__6);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_MessageData_ofSyntax(v_a_795_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v___x_796_, v_a_775_, v___x_802_);
return v___x_803_;
}
case 5:
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_a_804_ = lean_ctor_get(v_a_776_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v_a_776_, 2);
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__7));
v___x_806_ = lean_box(0);
v___x_807_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__0(v_a_804_, v___x_806_);
v___x_808_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__10);
v___x_809_ = l_Lean_MessageData_joinSep(v___x_807_, v___x_808_);
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__11));
v___x_811_ = l_Lean_MessageData_bracket(v___x_805_, v___x_809_, v___x_810_);
return v___x_811_;
}
default: 
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_812_ = lean_ctor_get(v_a_776_, 1);
lean_inc(v_a_812_);
lean_dec_ref_known(v_a_776_, 2);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_box(0);
v___x_815_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__1(v_a_812_, v___x_814_);
v___x_816_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__14);
v___x_817_ = l_Lean_MessageData_joinSep(v___x_815_, v___x_816_);
v___x_818_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_parenAbove(v___x_813_, v_a_775_, v___x_817_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt_spec__0(lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = l_List_reverse___redArg(v_a_820_);
return v___x_821_;
}
else
{
lean_object* v_head_822_; lean_object* v_tail_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_head_822_ = lean_ctor_get(v_a_819_, 0);
v_tail_823_ = lean_ctor_get(v_a_819_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v_a_819_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_tail_823_);
lean_inc(v_head_822_);
lean_dec(v_a_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v___x_827_, v_head_822_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_a_820_);
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_820_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_819_ = v_tail_823_;
v_a_820_ = v___x_830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___boxed(lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt(v_a_834_, v_a_835_);
lean_dec(v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(lean_object* v_ref_845_, lean_object* v_info_846_, uint8_t v_explicit_847_, lean_object* v_idx_848_, lean_object* v_ps_849_){
_start:
{
lean_object* v___y_851_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_883_; uint8_t v___x_902_; 
v___x_883_ = lean_array_get_size(v_info_846_);
v___x_902_ = lean_nat_dec_lt(v_idx_848_, v___x_883_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_ps_849_);
lean_dec(v_ref_845_);
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__1));
return v___x_903_;
}
else
{
if (v_explicit_847_ == 0)
{
lean_object* v___x_904_; uint8_t v_binderInfo_905_; uint8_t v___x_906_; uint8_t v___x_907_; 
v___x_904_ = lean_array_fget_borrowed(v_info_846_, v_idx_848_);
v_binderInfo_905_ = lean_ctor_get_uint8(v___x_904_, sizeof(void*)*1);
v___x_906_ = 0;
v___x_907_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_923_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_idx_848_, v___x_908_);
v___x_910_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_845_, v_info_846_, v_explicit_847_, v___x_909_, v_ps_849_);
lean_dec(v___x_909_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_923_ == 0)
{
v___x_914_ = v___x_910_;
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v___x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_923_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_fst_911_);
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_snd_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_919_);
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
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
goto v___jp_884_;
}
}
else
{
goto v___jp_884_;
}
}
v___jp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___y_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v_ps_849_);
return v___x_854_;
}
v___jp_855_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_859_);
lean_ctor_set(v___x_860_, 1, v___y_858_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_856_);
lean_ctor_set(v___x_861_, 1, v___y_857_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
v___jp_863_:
{
lean_object* v___x_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; 
v___x_867_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_845_, v_info_846_, v_explicit_847_, v___y_864_, v___y_866_);
lean_dec(v___y_864_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_snd_869_);
lean_dec_ref(v___x_867_);
v___x_870_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___y_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_856_ = v___y_865_;
v___y_857_ = v_snd_869_;
v___y_858_ = v_fst_868_;
v___y_859_ = v___x_871_;
goto v___jp_855_;
}
else
{
lean_object* v_val_872_; 
v_val_872_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_870_, 1);
v___y_856_ = v___y_865_;
v___y_857_ = v_snd_869_;
v___y_858_ = v_fst_868_;
v___y_859_ = v_val_872_;
goto v___jp_855_;
}
}
v___jp_873_:
{
if (lean_obj_tag(v_ps_849_) == 0)
{
v___y_864_ = v___y_874_;
v___y_865_ = v___y_875_;
v___y_866_ = v_ps_849_;
goto v___jp_863_;
}
else
{
lean_object* v_tail_876_; 
v_tail_876_ = lean_ctor_get(v_ps_849_, 1);
lean_inc(v_tail_876_);
lean_dec_ref_known(v_ps_849_, 2);
v___y_864_ = v___y_874_;
v___y_865_ = v___y_875_;
v___y_866_ = v_tail_876_;
goto v___jp_863_;
}
}
v___jp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___y_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
lean_inc(v___y_878_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___y_878_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
v___jp_884_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_idx_848_, v___x_885_);
v___x_887_ = lean_nat_dec_lt(v___x_886_, v___x_883_);
if (v___x_887_ == 0)
{
lean_dec(v___x_886_);
if (lean_obj_tag(v_ps_849_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_ref_845_);
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0));
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_ps_849_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_888_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_tail_892_; 
v_tail_892_ = lean_ctor_get(v_ps_849_, 1);
if (lean_obj_tag(v_tail_892_) == 0)
{
lean_object* v_head_893_; lean_object* v___x_894_; 
lean_dec(v_ref_845_);
v_head_893_ = lean_ctor_get(v_ps_849_, 0);
v___x_894_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_head_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_851_ = v___x_895_;
goto v___jp_850_;
}
else
{
lean_object* v_val_896_; 
v_val_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_894_, 1);
v___y_851_ = v_val_896_;
goto v___jp_850_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___closed__0));
lean_inc(v_ref_845_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v_ref_845_);
lean_ctor_set(v___x_898_, 1, v_ps_849_);
if (v_explicit_847_ == 0)
{
lean_dec(v_ref_845_);
v___y_878_ = v___x_897_;
v___y_879_ = v___x_898_;
goto v___jp_877_;
}
else
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_899_, 0, v_ref_845_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___y_878_ = v___x_897_;
v___y_879_ = v___x_899_;
goto v___jp_877_;
}
}
}
}
else
{
if (lean_obj_tag(v_ps_849_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_874_ = v___x_886_;
v___y_875_ = v___x_900_;
goto v___jp_873_;
}
else
{
lean_object* v_head_901_; 
v_head_901_ = lean_ctor_get(v_ps_849_, 0);
lean_inc(v_head_901_);
v___y_874_ = v___x_886_;
v___y_875_ = v_head_901_;
goto v___jp_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor___boxed(lean_object* v_ref_924_, lean_object* v_info_925_, lean_object* v_explicit_926_, lean_object* v_idx_927_, lean_object* v_ps_928_){
_start:
{
uint8_t v_explicit_boxed_929_; lean_object* v_res_930_; 
v_explicit_boxed_929_ = lean_unbox(v_explicit_926_);
v_res_930_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_924_, v_info_925_, v_explicit_boxed_929_, v_idx_927_, v_ps_928_);
lean_dec(v_idx_927_);
lean_dec_ref(v_info_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter___redArg(lean_object* v_x_931_, lean_object* v_h__1_932_){
_start:
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_935_; 
v_fst_933_ = lean_ctor_get(v_x_931_, 0);
lean_inc(v_fst_933_);
v_snd_934_ = lean_ctor_get(v_x_931_, 1);
lean_inc(v_snd_934_);
lean_dec_ref(v_x_931_);
v___x_935_ = lean_apply_2(v_h__1_932_, v_fst_933_, v_snd_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__1_splitter(lean_object* v_motive_936_, lean_object* v_x_937_, lean_object* v_h__1_938_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter___redArg(lean_object* v_ps_942_, lean_object* v_h__1_943_, lean_object* v_h__2_944_, lean_object* v_h__3_945_){
_start:
{
if (lean_obj_tag(v_ps_942_) == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_h__3_945_);
lean_dec(v_h__2_944_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_apply_1(v_h__1_943_, v___x_946_);
return v___x_947_;
}
else
{
lean_object* v_tail_948_; 
lean_dec(v_h__1_943_);
v_tail_948_ = lean_ctor_get(v_ps_942_, 1);
if (lean_obj_tag(v_tail_948_) == 0)
{
lean_object* v_head_949_; lean_object* v___x_950_; 
lean_dec(v_h__3_945_);
v_head_949_ = lean_ctor_get(v_ps_942_, 0);
lean_inc(v_head_949_);
lean_dec_ref_known(v_ps_942_, 2);
v___x_950_ = lean_apply_1(v_h__2_944_, v_head_949_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
lean_dec(v_h__2_944_);
v___x_951_ = lean_apply_3(v_h__3_945_, v_ps_942_, lean_box(0), lean_box(0));
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor_match__3_splitter(lean_object* v_motive_952_, lean_object* v_ps_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_, lean_object* v_h__3_956_){
_start:
{
if (lean_obj_tag(v_ps_953_) == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_h__3_956_);
lean_dec(v_h__2_955_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_apply_1(v_h__1_954_, v___x_957_);
return v___x_958_;
}
else
{
lean_object* v_tail_959_; 
lean_dec(v_h__1_954_);
v_tail_959_ = lean_ctor_get(v_ps_953_, 1);
if (lean_obj_tag(v_tail_959_) == 0)
{
lean_object* v_head_960_; lean_object* v___x_961_; 
lean_dec(v_h__3_956_);
v_head_960_ = lean_ctor_get(v_ps_953_, 0);
lean_inc(v_head_960_);
lean_dec_ref_known(v_ps_953_, 2);
v___x_961_ = lean_apply_1(v_h__2_955_, v_head_960_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; 
lean_dec(v_h__2_955_);
v___x_962_ = lean_apply_3(v_h__3_956_, v_ps_953_, lean_box(0), lean_box(0));
return v___x_962_;
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_963_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
lean_ctor_set(v___x_968_, 3, v___x_967_);
lean_ctor_set(v___x_968_, 4, v___x_966_);
lean_ctor_set(v___x_968_, 5, v___x_966_);
lean_ctor_set(v___x_968_, 6, v___x_966_);
lean_ctor_set(v___x_968_, 7, v___x_966_);
lean_ctor_set(v___x_968_, 8, v___x_966_);
lean_ctor_set(v___x_968_, 9, v___x_966_);
lean_ctor_set(v___x_968_, 10, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(32u);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((size_t)5ULL);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_unsigned_to_nat(32u);
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_974_);
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_977_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_975_);
lean_ctor_set(v___x_977_, 2, v___x_973_);
lean_ctor_set(v___x_977_, 3, v___x_973_);
lean_ctor_set_usize(v___x_977_, 4, v___x_972_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_box(1);
v___x_979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_978_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1003_, lean_object* v_declHint_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_env_1009_; uint8_t v___x_1010_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_st_ref_get(v___y_1005_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = l_Lean_Name_isAnonymous(v_declHint_1004_);
if (v___x_1010_ == 0)
{
uint8_t v_isExporting_1011_; 
v_isExporting_1011_ = lean_ctor_get_uint8(v_env_1009_, sizeof(void*)*13);
if (v_isExporting_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_msg_1003_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_inc_ref(v_env_1009_);
v___x_1013_ = l_Lean_Environment_setExporting(v_env_1009_, v___x_1010_);
lean_inc(v_declHint_1004_);
lean_inc_ref(v___x_1013_);
v___x_1014_ = l_Lean_Environment_contains(v___x_1013_, v_declHint_1004_, v_isExporting_1011_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_msg_1003_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_c_1021_; lean_object* v___x_1022_; 
v___x_1016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1018_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1013_);
v___x_1019_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1016_);
lean_ctor_set(v___x_1019_, 2, v___x_1017_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
lean_inc(v_declHint_1004_);
v___x_1020_ = l_Lean_MessageData_ofConstName(v_declHint_1004_, v___x_1010_);
v_c_1021_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1021_, 0, v___x_1019_);
lean_ctor_set(v_c_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1013_, v_declHint_1004_);
lean_dec_ref(v___x_1013_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_c_1021_);
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_MessageData_note(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_msg_1003_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1064_; 
v_val_1030_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1032_ = v___x_1022_;
v_isShared_1033_ = v_isSharedCheck_1064_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v___x_1022_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1064_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v_moduleNames_1035_; lean_object* v_mod_1036_; uint8_t v___x_1037_; 
v___x_1034_ = l_Lean_Environment_header(v_env_1009_);
lean_dec_ref(v_env_1009_);
v_moduleNames_1035_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_moduleNames_1035_);
lean_dec_ref(v___x_1034_);
v_mod_1036_ = lean_array_get(v___x_1007_, v_moduleNames_1035_, v_val_1030_);
lean_dec(v_val_1030_);
lean_dec_ref(v_moduleNames_1035_);
v___x_1037_ = l_Lean_isPrivateName(v_declHint_1004_);
lean_dec(v_declHint_1004_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_c_1021_);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_MessageData_ofName(v_mod_1036_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_MessageData_note(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_msg_1003_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1047_);
v___x_1049_ = v___x_1032_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_c_1021_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_MessageData_ofName(v_mod_1036_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_MessageData_note(v___x_1058_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_msg_1003_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1060_);
v___x_1062_ = v___x_1032_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1065_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_msg_1003_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1066_, lean_object* v_declHint_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1066_, v_declHint_1067_, v___y_1068_);
lean_dec(v___y_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_msg_1071_, lean_object* v_declHint_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1088_; 
v___x_1078_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1071_, v_declHint_1072_, v___y_1076_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = l_Lean_unknownIdentifierMessageTag;
v___x_1084_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1089_, lean_object* v_declHint_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1089_, v_declHint_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v_env_1104_; uint8_t v___x_1105_; lean_object* v_env_1106_; lean_object* v___x_1107_; lean_object* v_toCold_1108_; lean_object* v_mctx_1109_; lean_object* v_lctx_1110_; lean_object* v_options_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1103_ = lean_st_ref_get(v___y_1101_);
v_env_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc_ref(v_env_1104_);
lean_dec(v___x_1103_);
v___x_1105_ = 0;
v_env_1106_ = l_Lean_Environment_setRecordingDeps(v_env_1104_, v___x_1105_);
v___x_1107_ = lean_st_ref_get(v___y_1099_);
v_toCold_1108_ = lean_ctor_get(v___y_1100_, 0);
v_mctx_1109_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_mctx_1109_);
lean_dec(v___x_1107_);
v_lctx_1110_ = lean_ctor_get(v___y_1098_, 2);
v_options_1111_ = lean_ctor_get(v_toCold_1108_, 2);
lean_inc_ref(v_options_1111_);
lean_inc_ref(v_lctx_1110_);
v___x_1112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1112_, 0, v_env_1106_);
lean_ctor_set(v___x_1112_, 1, v_mctx_1109_);
lean_ctor_set(v___x_1112_, 2, v_lctx_1110_);
lean_ctor_set(v___x_1112_, 3, v_options_1111_);
v___x_1113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v_msgData_1097_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msgData_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_ref_1128_; lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_ref_1128_ = lean_ctor_get(v___y_1125_, 2);
v___x_1129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_inc(v_ref_1128_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_ref_1128_);
lean_ctor_set(v___x_1134_, 1, v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_toCold_1153_; lean_object* v_currRecDepth_1154_; lean_object* v_ref_1155_; uint16_t v_optionFlags_1156_; uint8_t v_suppressElabErrors_1157_; uint8_t v_checkDeprecated_1158_; uint8_t v_isRecordingDeps_1159_; lean_object* v_ref_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_toCold_1153_ = lean_ctor_get(v___y_1150_, 0);
v_currRecDepth_1154_ = lean_ctor_get(v___y_1150_, 1);
v_ref_1155_ = lean_ctor_get(v___y_1150_, 2);
v_optionFlags_1156_ = lean_ctor_get_uint16(v___y_1150_, sizeof(void*)*3);
v_suppressElabErrors_1157_ = lean_ctor_get_uint8(v___y_1150_, sizeof(void*)*3 + 2);
v_checkDeprecated_1158_ = lean_ctor_get_uint8(v___y_1150_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1159_ = lean_ctor_get_uint8(v___y_1150_, sizeof(void*)*3 + 4);
v_ref_1160_ = l_Lean_replaceRef(v_ref_1146_, v_ref_1155_);
lean_inc(v_currRecDepth_1154_);
lean_inc_ref(v_toCold_1153_);
v___x_1161_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1161_, 0, v_toCold_1153_);
lean_ctor_set(v___x_1161_, 1, v_currRecDepth_1154_);
lean_ctor_set(v___x_1161_, 2, v_ref_1160_);
lean_ctor_set_uint16(v___x_1161_, sizeof(void*)*3, v_optionFlags_1156_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 2, v_suppressElabErrors_1157_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 3, v_checkDeprecated_1158_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 4, v_isRecordingDeps_1159_);
v___x_1162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1147_, v___y_1148_, v___y_1149_, v___x_1161_, v___y_1151_);
lean_dec_ref_known(v___x_1161_, 3);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1163_, lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1163_, v_msg_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_ref_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1171_, lean_object* v_msg_1172_, lean_object* v_declHint_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1172_, v_declHint_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1171_, v_a_1180_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1182_, lean_object* v_msg_1183_, lean_object* v_declHint_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1182_, v_msg_1183_, v_declHint_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v_ref_1182_);
return v_res_1190_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1197_, lean_object* v_constName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1204_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1205_ = 0;
lean_inc(v_constName_1198_);
v___x_1206_ = l_Lean_MessageData_ofConstName(v_constName_1198_, v___x_1205_);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1204_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1197_, v___x_1209_, v_constName_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1211_, lean_object* v_constName_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1211_, v_constName_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v_ref_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_ref_1225_; lean_object* v___x_1226_; 
v_ref_1225_ = lean_ctor_get(v___y_1222_, 2);
v___x_1226_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1225_, v_constName_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object* v_constName_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v_env_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = lean_st_ref_get(v___y_1238_);
v_env_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc_ref(v_env_1241_);
lean_dec(v___x_1240_);
v___x_1242_ = 0;
lean_inc(v_constName_1234_);
v___x_1243_ = l_Lean_Environment_findConstVal_x3f(v_env_1241_, v_constName_1234_, v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_constName_1234_);
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 0);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
if (lean_obj_tag(v_a_1260_) == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = l_List_reverse___redArg(v_a_1261_);
return v___x_1262_;
}
else
{
lean_object* v_head_1263_; lean_object* v_tail_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1273_; 
v_head_1263_ = lean_ctor_get(v_a_1260_, 0);
v_tail_1264_ = lean_ctor_get(v_a_1260_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1266_ = v_a_1260_;
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_tail_1264_);
lean_inc(v_head_1263_);
lean_dec(v_a_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = l_Lean_mkLevelParam(v_head_1263_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_a_1261_);
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1261_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1260_ = v_tail_1264_;
v_a_1261_ = v___x_1270_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
lean_inc(v_constName_1274_);
v___x_1280_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_levelParams_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v_levelParams_1285_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_levelParams_1285_);
lean_dec(v_a_1281_);
v___x_1286_ = lean_box(0);
v___x_1287_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(v_levelParams_1285_, v___x_1286_);
v___x_1288_ = l_Lean_mkConst(v_constName_1274_, v___x_1287_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_constName_1274_);
v_a_1293_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1280_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1280_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object* v_constName_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_constName_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object* v_ref_1308_, lean_object* v_params_1309_, lean_object* v_altVarNames_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_x_1312_);
lean_dec(v_ref_1308_);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_altVarNames_1310_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
else
{
lean_object* v_head_1321_; lean_object* v_tail_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1428_; 
v_head_1321_ = lean_ctor_get(v_x_1311_, 0);
v_tail_1322_ = lean_ctor_get(v_x_1311_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1324_ = v_x_1311_;
v_isShared_1325_ = v_isSharedCheck_1428_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_tail_1322_);
lean_inc(v_head_1321_);
lean_dec(v_x_1311_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1428_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; 
lean_inc(v_head_1321_);
v___x_1326_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_head_1321_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = lean_box(0);
v___x_1329_ = l_Lean_Meta_getFunInfo(v_a_1327_, v___x_1328_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_paramInfo_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1410_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_paramInfo_1331_ = lean_ctor_get(v_a_1330_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v_a_1330_, 1);
lean_dec(v_unused_1411_);
v___x_1333_ = v_a_1330_;
v_isShared_1334_ = v_isSharedCheck_1410_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_paramInfo_1331_);
lean_dec(v_a_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1410_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1375_; uint8_t v_fst_1376_; lean_object* v_snd_1377_; lean_object* v_snd_1378_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1405_; 
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_1405_ = v___x_1408_;
goto v___jp_1404_;
}
else
{
lean_object* v_head_1409_; 
v_head_1409_ = lean_ctor_get(v_x_1312_, 0);
lean_inc(v_head_1409_);
v___y_1405_ = v_head_1409_;
goto v___jp_1404_;
}
v___jp_1335_:
{
lean_object* v___x_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1373_; 
v___x_1340_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1339_, v_paramInfo_1331_, v___y_1338_, v_params_1309_, v___y_1337_);
lean_dec_ref(v_paramInfo_1331_);
v_fst_1341_ = lean_ctor_get(v___x_1340_, 0);
v_snd_1342_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1373_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1373_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = 1;
v___x_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1347_, 0, v_fst_1341_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v___x_1346_);
v___x_1348_ = lean_array_push(v_altVarNames_1310_, v___x_1347_);
v___x_1349_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1308_, v_params_1309_, v___x_1348_, v_tail_1322_, v___y_1336_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1372_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1372_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1372_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1371_; 
v_fst_1354_ = lean_ctor_get(v_a_1350_, 0);
v_snd_1355_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1357_ = v_a_1350_;
v_isShared_1358_ = v_isSharedCheck_1371_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v_a_1350_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1371_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_snd_1342_);
lean_ctor_set(v___x_1357_, 0, v_head_1321_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_head_1321_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_snd_1342_);
v___x_1360_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_snd_1355_);
lean_ctor_set(v___x_1324_, 0, v___x_1360_);
v___x_1362_ = v___x_1324_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_snd_1355_);
v___x_1362_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1362_);
lean_ctor_set(v___x_1344_, 0, v_fst_1354_);
v___x_1364_ = v___x_1344_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1364_);
v___x_1366_ = v___x_1352_;
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
}
}
}
}
else
{
lean_del_object(v___x_1344_);
lean_dec(v_snd_1342_);
lean_del_object(v___x_1324_);
lean_dec(v_head_1321_);
return v___x_1349_;
}
}
}
v___jp_1374_:
{
lean_object* v_ref_1379_; 
v_ref_1379_ = lean_ctor_get(v___y_1375_, 0);
lean_inc(v_ref_1379_);
lean_dec_ref(v___y_1375_);
v___y_1336_ = v_snd_1378_;
v___y_1337_ = v_snd_1377_;
v___y_1338_ = v_fst_1376_;
v___y_1339_ = v_ref_1379_;
goto v___jp_1335_;
}
v___jp_1380_:
{
lean_object* v___x_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; uint8_t v___x_1386_; 
lean_inc_ref(v___y_1382_);
v___x_1383_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1382_);
v_fst_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_snd_1385_);
lean_dec_ref(v___x_1383_);
v___x_1386_ = lean_unbox(v_fst_1384_);
lean_dec(v_fst_1384_);
v___y_1375_ = v___y_1382_;
v_fst_1376_ = v___x_1386_;
v_snd_1377_ = v_snd_1385_;
v_snd_1378_ = v___y_1381_;
goto v___jp_1374_;
}
v___jp_1387_:
{
if (lean_obj_tag(v_tail_1322_) == 0)
{
if (lean_obj_tag(v___y_1390_) == 1)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1402_ = lean_ctor_get(v___y_1390_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v___y_1390_, 0);
lean_dec(v_unused_1403_);
v___x_1392_ = v___y_1390_;
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___y_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint8_t v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = 0;
lean_inc(v_ref_1308_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 6);
lean_ctor_set(v___x_1333_, 1, v_x_1312_);
lean_ctor_set(v___x_1333_, 0, v_ref_1308_);
v___x_1396_ = v___x_1333_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_ref_1308_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_x_1312_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
lean_inc(v___y_1388_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___y_1388_);
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___y_1388_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1375_ = v___y_1389_;
v_fst_1376_ = v___x_1394_;
v_snd_1377_ = v___x_1398_;
v_snd_1378_ = v___y_1388_;
goto v___jp_1374_;
}
}
}
}
else
{
lean_dec(v___y_1388_);
lean_del_object(v___x_1333_);
lean_dec(v_x_1312_);
v___y_1381_ = v___y_1390_;
v___y_1382_ = v___y_1389_;
goto v___jp_1380_;
}
}
else
{
lean_dec(v___y_1388_);
lean_del_object(v___x_1333_);
lean_dec(v_x_1312_);
v___y_1381_ = v___y_1390_;
v___y_1382_ = v___y_1389_;
goto v___jp_1380_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_box(0);
if (lean_obj_tag(v_x_1312_) == 0)
{
v___y_1388_ = v___x_1406_;
v___y_1389_ = v___y_1405_;
v___y_1390_ = v___x_1406_;
goto v___jp_1387_;
}
else
{
lean_object* v_tail_1407_; 
v_tail_1407_ = lean_ctor_get(v_x_1312_, 1);
lean_inc(v_tail_1407_);
v___y_1388_ = v___x_1406_;
v___y_1389_ = v___y_1405_;
v___y_1390_ = v_tail_1407_;
goto v___jp_1387_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_del_object(v___x_1324_);
lean_dec(v_tail_1322_);
lean_dec(v_head_1321_);
lean_dec(v_x_1312_);
lean_dec_ref(v_altVarNames_1310_);
lean_dec(v_ref_1308_);
v_a_1412_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1329_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1329_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1324_);
lean_dec(v_tail_1322_);
lean_dec(v_head_1321_);
lean_dec(v_x_1312_);
lean_dec_ref(v_altVarNames_1310_);
lean_dec(v_ref_1308_);
v_a_1420_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1326_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1326_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object* v_ref_1429_, lean_object* v_params_1430_, lean_object* v_altVarNames_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1429_, v_params_1430_, v_altVarNames_1431_, v_x_1432_, v_x_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_params_1430_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1440_, lean_object* v_constName_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1448_, lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(v_00_u03b1_1448_, v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1456_, lean_object* v_ref_1457_, lean_object* v_constName_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1457_, v_constName_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_ref_1466_, lean_object* v_constName_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1465_, v_ref_1466_, v_constName_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_ref_1466_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1474_, lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v_declHint_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1475_, v_msg_1476_, v_declHint_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_ref_1485_, lean_object* v_msg_1486_, lean_object* v_declHint_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1484_, v_ref_1485_, v_msg_1486_, v_declHint_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v_ref_1485_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_1494_, lean_object* v_declHint_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1494_, v_declHint_1495_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1502_, lean_object* v_declHint_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(v_msg_1502_, v_declHint_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1510_, lean_object* v_ref_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_ref_1520_, lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1519_, v_ref_1520_, v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v_ref_1520_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1528_, lean_object* v_msg_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_msg_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1536_, v_msg_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object* v_e_1544_, lean_object* v_cont_1545_, lean_object* v_g_1546_, lean_object* v_fs_1547_, lean_object* v_clears_1548_, lean_object* v_a_1549_, lean_object* v_ref_1550_, lean_object* v_a_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_Expr_isFVar(v_e_1544_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec(v_ref_1550_);
lean_dec_ref(v_e_1544_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
v___x_1560_ = lean_apply_11(v_cont_1545_, v_g_1546_, v_fs_1547_, v_clears_1548_, v_a_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, lean_box(0));
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_1550_, v_e_1544_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; 
lean_dec_ref_known(v___x_1561_, 1);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
v___x_1562_ = lean_apply_11(v_cont_1545_, v_g_1546_, v_fs_1547_, v_clears_1548_, v_a_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, lean_box(0));
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1549_);
lean_dec_ref(v_clears_1548_);
lean_dec(v_fs_1547_);
lean_dec(v_g_1546_);
lean_dec_ref(v_cont_1545_);
v_a_1563_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1561_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object* v_e_1571_, lean_object* v_cont_1572_, lean_object* v_g_1573_, lean_object* v_fs_1574_, lean_object* v_clears_1575_, lean_object* v_a_1576_, lean_object* v_ref_1577_, lean_object* v_a_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(v_e_1571_, v_cont_1572_, v_g_1573_, v_fs_1574_, v_clears_1575_, v_a_1576_, v_ref_1577_, v_a_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v_a_1578_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object* v_x_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
v___x_1595_ = lean_apply_7(v_x_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(v_x_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object* v_mvarId_1605_, lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; 
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1614_, 0, v_x_1606_);
lean_closure_set(v___f_1614_, 1, v___y_1607_);
lean_closure_set(v___f_1614_, 2, v___y_1608_);
v___x_1615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1605_, v___f_1614_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
return v___x_1615_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object* v_mvarId_1624_, lean_object* v_x_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_1624_, v_x_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1633_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0));
v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 1)
{
lean_object* v_fvarId_1646_; lean_object* v___x_1647_; 
v_fvarId_1646_ = lean_ctor_get(v_x_1640_, 0);
lean_inc(v_fvarId_1646_);
lean_dec_ref_known(v_x_1640_, 1);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_fvarId_1646_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1649_ = l_Lean_MessageData_ofExpr(v_x_1640_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v___x_1652_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object* v_x_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(v_x_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1660_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_1665_ = l_Lean_MessageData_ofFormat(v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
return v_x_1666_;
}
else
{
lean_object* v_head_1668_; lean_object* v_tail_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1691_; 
v_head_1668_ = lean_ctor_get(v_x_1667_, 0);
v_tail_1669_ = lean_ctor_get(v_x_1667_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1671_ = v_x_1667_;
v_isShared_1672_ = v_isSharedCheck_1691_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_tail_1669_);
lean_inc(v_head_1668_);
lean_dec(v_x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1691_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_before_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1689_; 
v_before_1673_ = lean_ctor_get(v_head_1668_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_head_1668_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; 
v_unused_1690_ = lean_ctor_get(v_head_1668_, 1);
lean_dec(v_unused_1690_);
v___x_1675_ = v_head_1668_;
v_isShared_1676_ = v_isSharedCheck_1689_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_before_1673_);
lean_dec(v_head_1668_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1689_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 7);
lean_ctor_set(v___x_1675_, 1, v___x_1677_);
lean_ctor_set(v___x_1675_, 0, v_x_1666_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_x_1666_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 7);
lean_ctor_set(v___x_1671_, 1, v___x_1680_);
lean_ctor_set(v___x_1671_, 0, v___x_1679_);
v___x_1682_ = v___x_1671_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_MessageData_ofSyntax(v_before_1673_);
v___x_1684_ = l_Lean_indentD(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v_x_1666_ = v___x_1685_;
v_x_1667_ = v_tail_1669_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_1692_, lean_object* v_opt_1693_){
_start:
{
lean_object* v_name_1694_; lean_object* v_defValue_1695_; lean_object* v_map_1696_; lean_object* v___x_1697_; 
v_name_1694_ = lean_ctor_get(v_opt_1693_, 0);
v_defValue_1695_ = lean_ctor_get(v_opt_1693_, 1);
v_map_1696_ = lean_ctor_get(v_opts_1692_, 0);
v___x_1697_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1696_, v_name_1694_);
if (lean_obj_tag(v___x_1697_) == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_unbox(v_defValue_1695_);
return v___x_1698_;
}
else
{
lean_object* v_val_1699_; 
v_val_1699_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v___x_1697_, 1);
if (lean_obj_tag(v_val_1699_) == 1)
{
uint8_t v_v_1700_; 
v_v_1700_ = lean_ctor_get_uint8(v_val_1699_, 0);
lean_dec_ref_known(v_val_1699_, 0);
return v_v_1700_;
}
else
{
uint8_t v___x_1701_; 
lean_dec(v_val_1699_);
v___x_1701_ = lean_unbox(v_defValue_1695_);
return v___x_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_1702_, lean_object* v_opt_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_1702_, v_opt_1703_);
lean_dec_ref(v_opt_1703_);
lean_dec_ref(v_opts_1702_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_1710_ = l_Lean_MessageData_ofFormat(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_1711_, lean_object* v_macroStack_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1713_);
v___x_1716_ = l_Lean_Elab_pp_macroStack;
v___x_1717_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v___x_1715_, v___x_1716_);
lean_dec_ref(v___x_1715_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_macroStack_1712_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_msgData_1711_);
return v___x_1718_;
}
else
{
if (lean_obj_tag(v_macroStack_1712_) == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_msgData_1711_);
return v___x_1719_;
}
else
{
lean_object* v_head_1720_; lean_object* v_after_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1736_; 
v_head_1720_ = lean_ctor_get(v_macroStack_1712_, 0);
lean_inc(v_head_1720_);
v_after_1721_ = lean_ctor_get(v_head_1720_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_head_1720_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v_head_1720_, 0);
lean_dec(v_unused_1737_);
v___x_1723_ = v_head_1720_;
v_isShared_1724_ = v_isSharedCheck_1736_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_after_1721_);
lean_dec(v_head_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1736_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 7);
lean_ctor_set(v___x_1723_, 1, v___x_1725_);
lean_ctor_set(v___x_1723_, 0, v_msgData_1711_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_msgData_1711_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_msgData_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1728_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_MessageData_ofSyntax(v_after_1721_);
v___x_1731_ = l_Lean_indentD(v___x_1730_);
v_msgData_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1732_, 0, v___x_1729_);
lean_ctor_set(v_msgData_1732_, 1, v___x_1731_);
v___x_1733_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_1732_, v_macroStack_1712_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_1738_, lean_object* v_macroStack_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_1738_, v_macroStack_1739_, v___y_1740_);
lean_dec_ref(v___y_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_ref_1751_; lean_object* v_macroStack_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_ref_1751_ = lean_ctor_get(v___y_1748_, 2);
v_macroStack_1752_ = lean_ctor_get(v___y_1744_, 1);
v___x_1753_ = l_Lean_Elab_getBetterRef(v_ref_1751_, v_macroStack_1752_);
v___x_1754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1743_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
lean_inc(v_macroStack_1752_);
v___x_1756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_1755_, v_macroStack_1752_, v___y_1748_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1753_);
lean_ctor_set(v___x_1761_, 1, v_a_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 1);
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
return v_res_1774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0));
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(lean_object* v_e_1781_, lean_object* v_a_1782_, lean_object* v_00_u03b1_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1793_ = l_Lean_MessageData_ofExpr(v_e_1781_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_MessageData_ofExpr(v_a_1782_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_1800_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v_e_1802_, lean_object* v_a_1803_, lean_object* v_00_u03b1_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_1802_, v_a_1803_, v_00_u03b1_1804_, v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1813_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
if (lean_obj_tag(v_x_1814_) == 0)
{
if (lean_obj_tag(v_x_1815_) == 0)
{
uint8_t v___x_1816_; 
v___x_1816_ = 1;
return v___x_1816_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = 0;
return v___x_1817_;
}
}
else
{
if (lean_obj_tag(v_x_1815_) == 0)
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v_val_1820_; uint8_t v___x_1821_; 
v_val_1819_ = lean_ctor_get(v_x_1814_, 0);
v_val_1820_ = lean_ctor_get(v_x_1815_, 0);
v___x_1821_ = lean_name_eq(v_val_1819_, v_val_1820_);
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
uint8_t v_res_1824_; lean_object* v_r_1825_; 
v_res_1824_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_1822_, v_x_1823_);
lean_dec(v_x_1823_);
lean_dec(v_x_1822_);
v_r_1825_ = lean_box(v_res_1824_);
return v_r_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___lam__0(lean_object* v_fst_1826_, lean_object* v_snd_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_fst_1826_);
lean_ctor_set(v___x_1828_, 1, v_snd_1827_);
return v___x_1828_;
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
size_t v_x_18607__boxed_1968_; size_t v_x_18608__boxed_1969_; lean_object* v_res_1970_; 
v_x_18607__boxed_1968_ = lean_unbox_usize(v_x_1964_);
lean_dec(v_x_1964_);
v_x_18608__boxed_1969_ = lean_unbox_usize(v_x_1965_);
lean_dec(v_x_1965_);
v_res_1970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1963_, v_x_18607__boxed_1968_, v_x_18608__boxed_1969_, v_x_1966_, v_x_1967_);
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
lean_object* v___x_2031_; lean_object* v___x_14826__overap_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_14826__overap_2032_ = lean_panic_fn_borrowed(v___x_2031_, v_msg_2023_);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
v___x_2033_ = lean_apply_7(v___x_14826__overap_2032_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, lean_box(0));
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
lean_object* v___x_2122_; lean_object* v_name_2123_; lean_object* v_mvarId_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2192_; 
v___x_2122_ = lean_array_fget(v_alts_2103_, v___x_2081_);
lean_dec_ref(v_alts_2103_);
v_name_2123_ = lean_ctor_get(v___x_2122_, 0);
v_mvarId_2124_ = lean_ctor_get(v___x_2122_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v___x_2122_, 1);
lean_dec(v_unused_2193_);
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2192_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_mvarId_2124_);
lean_inc(v_name_2123_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2192_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_MVarId_intro(v_mvarId_2124_, v_head_2082_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v_fst_2130_; lean_object* v_snd_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2183_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v_fst_2130_ = lean_ctor_get(v_a_2129_, 0);
v_snd_2131_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2133_ = v_a_2129_;
v_isShared_2134_ = v_isSharedCheck_2183_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_snd_2131_);
lean_inc(v_fst_2130_);
lean_dec(v_a_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2183_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_array_get_size(v_fst_2083_);
v___x_2136_ = l_Lean_Meta_introNCore(v_snd_2131_, v___x_2135_, v_tail_2084_, v___x_2085_, v___x_2119_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2174_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2174_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2174_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2173_; 
v_fst_2141_ = lean_ctor_get(v_a_2137_, 0);
v_snd_2142_ = lean_ctor_get(v_a_2137_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2137_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2144_ = v_a_2137_;
v_isShared_2145_ = v_isSharedCheck_2173_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_snd_2142_);
lean_inc(v_fst_2141_);
lean_dec(v_a_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2173_;
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
size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((size_t)0ULL);
v___x_2171_ = lean_usize_of_nat(v___x_2168_);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2167_, v___x_2170_, v___x_2171_, v_fs_2088_);
lean_dec_ref(v___x_2167_);
v___y_2147_ = v___x_2172_;
goto v___jp_2146_;
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
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2133_);
lean_dec(v_fst_2130_);
lean_del_object(v___x_2126_);
lean_dec(v_name_2123_);
lean_dec_ref(v___x_2113_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
v_a_2175_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2136_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2136_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_del_object(v___x_2126_);
lean_dec(v_name_2123_);
lean_dec_ref(v___x_2113_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
v_a_2184_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2128_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2128_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
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
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_alts_2103_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
v_a_2194_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2117_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2117_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_alts_2103_);
lean_dec_ref(v_elimApp_2102_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec(v_snd_2076_);
v_a_2202_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2116_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2116_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2097_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec(v_snd_2076_);
v_a_2210_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2100_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2100_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2097_);
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec_ref(v___x_2077_);
lean_dec(v_snd_2076_);
v_a_2218_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2098_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2098_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_fs_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_snd_2086_);
lean_dec(v_tail_2084_);
lean_dec(v_head_2082_);
lean_dec_ref(v___x_2077_);
lean_dec(v_snd_2076_);
v_a_2226_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2096_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2096_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2234_ = _args[0];
lean_object* v___x_2235_ = _args[1];
lean_object* v_snd_2236_ = _args[2];
lean_object* v___x_2237_ = _args[3];
lean_object* v___x_2238_ = _args[4];
lean_object* v___x_2239_ = _args[5];
lean_object* v_e_2240_ = _args[6];
lean_object* v___x_2241_ = _args[7];
lean_object* v_head_2242_ = _args[8];
lean_object* v_fst_2243_ = _args[9];
lean_object* v_tail_2244_ = _args[10];
lean_object* v___x_2245_ = _args[11];
lean_object* v_snd_2246_ = _args[12];
lean_object* v___x_2247_ = _args[13];
lean_object* v_fs_2248_ = _args[14];
lean_object* v___y_2249_ = _args[15];
lean_object* v___y_2250_ = _args[16];
lean_object* v___y_2251_ = _args[17];
lean_object* v___y_2252_ = _args[18];
lean_object* v___y_2253_ = _args[19];
lean_object* v___y_2254_ = _args[20];
lean_object* v___y_2255_ = _args[21];
_start:
{
uint8_t v___x_18892__boxed_2256_; lean_object* v_res_2257_; 
v___x_18892__boxed_2256_ = lean_unbox(v___x_2245_);
v_res_2257_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v___x_2234_, v___x_2235_, v_snd_2236_, v___x_2237_, v___x_2238_, v___x_2239_, v_e_2240_, v___x_2241_, v_head_2242_, v_fst_2243_, v_tail_2244_, v___x_18892__boxed_2256_, v_snd_2246_, v___x_2247_, v_fs_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_fst_2243_);
lean_dec(v___x_2241_);
lean_dec_ref(v_e_2240_);
lean_dec_ref(v___x_2239_);
lean_dec(v___x_2238_);
return v_res_2257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2259_ = lean_unsigned_to_nat(76u);
v___x_2260_ = lean_unsigned_to_nat(315u);
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2263_ = l_mkPanicMessageWithDecl(v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(uint8_t v___x_2271_, lean_object* v_e_2272_, lean_object* v___x_2273_, lean_object* v_g_2274_, lean_object* v___x_2275_, lean_object* v_fs_2276_, lean_object* v_pat_2277_, lean_object* v_____r_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___y_2290_; uint8_t v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2334_; lean_object* v___x_2340_; 
v___x_2340_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2277_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2341_; 
v___x_2341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2334_ = v___x_2341_;
goto v___jp_2333_;
}
else
{
lean_object* v_head_2342_; 
v_head_2342_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_head_2342_);
lean_dec_ref_known(v___x_2340_, 2);
v___y_2334_ = v_head_2342_;
goto v___jp_2333_;
}
v___jp_2286_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
v___x_2288_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2287_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2288_;
}
v___jp_2289_:
{
uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v_fst_2301_; 
v___x_2293_ = 0;
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2296_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1, v___x_2293_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 1, v___x_2271_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 2, v___x_2271_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 3, v___x_2271_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 4, v___x_2271_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 5, v___x_2271_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1 + 6, v___x_2271_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___x_2297_);
lean_inc_ref(v___x_2298_);
v___x_2299_ = lean_array_push(v___x_2298_, v___x_2296_);
v___x_2300_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2292_, v___x_2299_, v___y_2291_, v___x_2294_, v___y_2290_);
lean_dec_ref(v___x_2299_);
v_fst_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_fst_2301_);
if (lean_obj_tag(v_fst_2301_) == 1)
{
lean_object* v_tail_2302_; 
v_tail_2302_ = lean_ctor_get(v_fst_2301_, 1);
lean_inc(v_tail_2302_);
if (lean_obj_tag(v_tail_2302_) == 0)
{
lean_object* v_snd_2303_; lean_object* v_head_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_snd_2303_ = lean_ctor_get(v___x_2300_, 1);
lean_inc(v_snd_2303_);
lean_dec_ref(v___x_2300_);
v_head_2304_ = lean_ctor_get(v_fst_2301_, 0);
lean_inc(v_head_2304_);
lean_dec_ref_known(v_fst_2301_, 2);
lean_inc_ref(v_e_2272_);
lean_inc_ref(v___x_2298_);
v___x_2305_ = lean_array_push(v___x_2298_, v_e_2272_);
v___x_2306_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2305_, v___x_2273_, v___x_2271_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = l_Lean_MVarId_revert(v_g_2274_, v_a_2307_, v___x_2271_, v___x_2271_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v_fst_2310_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v_a_2309_, 1);
lean_inc_n(v_snd_2311_, 2);
lean_dec(v_a_2309_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4));
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_box(v___x_2271_);
v___f_2315_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed), 22, 15);
lean_closure_set(v___f_2315_, 0, v___x_2312_);
lean_closure_set(v___f_2315_, 1, v___x_2313_);
lean_closure_set(v___f_2315_, 2, v_snd_2311_);
lean_closure_set(v___f_2315_, 3, v___x_2305_);
lean_closure_set(v___f_2315_, 4, v___x_2297_);
lean_closure_set(v___f_2315_, 5, v___x_2275_);
lean_closure_set(v___f_2315_, 6, v_e_2272_);
lean_closure_set(v___f_2315_, 7, v___x_2294_);
lean_closure_set(v___f_2315_, 8, v_head_2304_);
lean_closure_set(v___f_2315_, 9, v_fst_2310_);
lean_closure_set(v___f_2315_, 10, v_tail_2302_);
lean_closure_set(v___f_2315_, 11, v___x_2314_);
lean_closure_set(v___f_2315_, 12, v_snd_2303_);
lean_closure_set(v___f_2315_, 13, v___x_2298_);
lean_closure_set(v___f_2315_, 14, v_fs_2276_);
v___x_2316_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2311_, v___f_2315_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2316_;
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v___x_2305_);
lean_dec(v_head_2304_);
lean_dec(v_snd_2303_);
lean_dec_ref(v___x_2298_);
lean_dec(v_fs_2276_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_e_2272_);
v_a_2317_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2308_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2308_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v___x_2305_);
lean_dec(v_head_2304_);
lean_dec(v_snd_2303_);
lean_dec_ref(v___x_2298_);
lean_dec(v_fs_2276_);
lean_dec_ref(v___x_2275_);
lean_dec(v_g_2274_);
lean_dec_ref(v_e_2272_);
v_a_2325_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2306_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2306_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_dec(v_tail_2302_);
lean_dec_ref_known(v_fst_2301_, 2);
lean_dec_ref(v___x_2300_);
lean_dec_ref(v___x_2298_);
lean_dec(v_fs_2276_);
lean_dec_ref(v___x_2275_);
lean_dec(v_g_2274_);
lean_dec(v___x_2273_);
lean_dec_ref(v_e_2272_);
goto v___jp_2286_;
}
}
else
{
lean_dec(v_fst_2301_);
lean_dec_ref(v___x_2300_);
lean_dec_ref(v___x_2298_);
lean_dec(v_fs_2276_);
lean_dec_ref(v___x_2275_);
lean_dec(v_g_2274_);
lean_dec(v___x_2273_);
lean_dec_ref(v_e_2272_);
goto v___jp_2286_;
}
}
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v_fst_2336_; lean_object* v_snd_2337_; lean_object* v_ref_2338_; uint8_t v___x_2339_; 
lean_inc_ref(v___y_2334_);
v___x_2335_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2334_);
v_fst_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_fst_2336_);
v_snd_2337_ = lean_ctor_get(v___x_2335_, 1);
lean_inc(v_snd_2337_);
lean_dec_ref(v___x_2335_);
v_ref_2338_ = lean_ctor_get(v___y_2334_, 0);
lean_inc(v_ref_2338_);
lean_dec_ref(v___y_2334_);
v___x_2339_ = lean_unbox(v_fst_2336_);
lean_dec(v_fst_2336_);
v___y_2290_ = v_snd_2337_;
v___y_2291_ = v___x_2339_;
v___y_2292_ = v_ref_2338_;
goto v___jp_2289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object* v___x_2343_, lean_object* v_e_2344_, lean_object* v___x_2345_, lean_object* v_g_2346_, lean_object* v___x_2347_, lean_object* v_fs_2348_, lean_object* v_pat_2349_, lean_object* v_____r_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v___x_19256__boxed_2358_; lean_object* v_res_2359_; 
v___x_19256__boxed_2358_ = lean_unbox(v___x_2343_);
v_res_2359_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_19256__boxed_2358_, v_e_2344_, v___x_2345_, v_g_2346_, v___x_2347_, v_fs_2348_, v_pat_2349_, v_____r_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2360_, lean_object* v_cont_2361_, lean_object* v_g_2362_, lean_object* v_fs_2363_, lean_object* v_clears_2364_, lean_object* v_a_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2360_, v_cont_2361_, v_g_2362_, v_fs_2363_, v_clears_2364_, v_a_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2375_, lean_object* v_g_2376_, lean_object* v_fs_2377_, lean_object* v_clears_2378_, lean_object* v_a_2379_, lean_object* v_cont_2380_, lean_object* v_ref_2381_, lean_object* v_p_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; 
v___x_2390_ = lean_box(0);
lean_inc_ref(v_e_2375_);
v___x_2391_ = l_Lean_Expr_mdata___override(v___x_2390_, v_e_2375_);
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_box(0);
v___x_2394_ = 0;
v___x_2395_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2381_, v___x_2391_, v___x_2392_, v___x_2392_, v___x_2393_, v___x_2394_, v___x_2394_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref_known(v___x_2395_, 1);
v___x_2396_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2376_, v_fs_2377_, v_clears_2378_, v_e_2375_, v_a_2379_, v_p_2382_, v_cont_2380_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec_ref(v_e_2375_);
return v___x_2396_;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_p_2382_);
lean_dec_ref(v_cont_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_clears_2378_);
lean_dec(v_fs_2377_);
lean_dec(v_g_2376_);
lean_dec_ref(v_e_2375_);
v_a_2397_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2395_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2405_, lean_object* v_g_2406_, lean_object* v_fs_2407_, lean_object* v_clears_2408_, lean_object* v_a_2409_, lean_object* v_cont_2410_, lean_object* v_ref_2411_, lean_object* v_p_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2405_, v_g_2406_, v_fs_2407_, v_clears_2408_, v_a_2409_, v_cont_2410_, v_ref_2411_, v_p_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2424_, lean_object* v_clears_2425_, lean_object* v_cont_2426_, lean_object* v_a_2427_, lean_object* v_goal_2428_, lean_object* v_ctorName_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
if (lean_obj_tag(v_a_2430_) == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec_ref(v_goal_2428_);
lean_dec_ref(v_cont_2426_);
lean_dec_ref(v_clears_2425_);
lean_dec(v_fs_2424_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2430_);
lean_ctor_set(v___x_2438_, 1, v_a_2427_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
else
{
lean_object* v_head_2440_; lean_object* v_tail_2441_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2478_; 
v_head_2440_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_head_2440_);
v_tail_2441_ = lean_ctor_get(v_a_2430_, 1);
lean_inc(v_tail_2441_);
lean_dec_ref_known(v_a_2430_, 2);
v_fst_2442_ = lean_ctor_get(v_head_2440_, 0);
v_snd_2443_ = lean_ctor_get(v_head_2440_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_head_2440_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2445_ = v_head_2440_;
v_isShared_2446_ = v_isSharedCheck_2478_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snd_2443_);
lean_inc(v_fst_2442_);
lean_dec(v_head_2440_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2478_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2447_, 0, v_fst_2442_);
v___x_2448_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2447_, v_ctorName_2429_);
lean_dec_ref_known(v___x_2447_, 1);
if (v___x_2448_ == 0)
{
lean_del_object(v___x_2445_);
lean_dec(v_snd_2443_);
v_a_2430_ = v_tail_2441_;
goto _start;
}
else
{
lean_object* v_mvarId_2450_; lean_object* v_fields_2451_; lean_object* v_subst_2452_; lean_object* v___f_2453_; lean_object* v_fs_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_mvarId_2450_ = lean_ctor_get(v_goal_2428_, 0);
lean_inc(v_mvarId_2450_);
v_fields_2451_ = lean_ctor_get(v_goal_2428_, 1);
lean_inc_ref(v_fields_2451_);
v_subst_2452_ = lean_ctor_get(v_goal_2428_, 2);
lean_inc(v_subst_2452_);
lean_dec_ref(v_goal_2428_);
v___f_2453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__0));
v_fs_2454_ = l_Lean_Meta_FVarSubst_append(v_fs_2424_, v_subst_2452_);
v___x_2455_ = lean_array_to_list(v_fields_2451_);
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___closed__1));
v___x_2457_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2453_, v_snd_2443_, v___x_2455_, v___x_2456_);
v___x_2458_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2450_, v_fs_2454_, v_clears_2425_, v_a_2427_, v___x_2457_, v_cont_2426_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2469_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2469_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2469_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 1, v_a_2459_);
lean_ctor_set(v___x_2445_, 0, v_tail_2441_);
v___x_2464_ = v___x_2445_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_tail_2441_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2464_);
v___x_2466_ = v___x_2461_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2445_);
lean_dec(v_tail_2441_);
v_a_2470_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2458_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2458_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2479_, lean_object* v_clears_2480_, lean_object* v_cont_2481_, lean_object* v_as_2482_, size_t v_i_2483_, size_t v_stop_2484_, lean_object* v_b_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_eq(v_i_2483_, v_stop_2484_);
if (v___x_2493_ == 0)
{
lean_object* v_fst_2494_; lean_object* v_snd_2495_; lean_object* v___x_2496_; lean_object* v_toInductionSubgoal_2497_; lean_object* v_ctorName_2498_; lean_object* v___x_2499_; 
v_fst_2494_ = lean_ctor_get(v_b_2485_, 0);
lean_inc(v_fst_2494_);
v_snd_2495_ = lean_ctor_get(v_b_2485_, 1);
lean_inc(v_snd_2495_);
lean_dec_ref(v_b_2485_);
v___x_2496_ = lean_array_uget_borrowed(v_as_2482_, v_i_2483_);
v_toInductionSubgoal_2497_ = lean_ctor_get(v___x_2496_, 0);
v_ctorName_2498_ = lean_ctor_get(v___x_2496_, 1);
lean_inc_ref(v_toInductionSubgoal_2497_);
lean_inc_ref(v_cont_2481_);
lean_inc_ref(v_clears_2480_);
lean_inc(v_fs_2479_);
v___x_2499_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2479_, v_clears_2480_, v_cont_2481_, v_snd_2495_, v_toInductionSubgoal_2497_, v_ctorName_2498_, v_fst_2494_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; size_t v___x_2501_; size_t v___x_2502_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_add(v_i_2483_, v___x_2501_);
v_i_2483_ = v___x_2502_;
v_b_2485_ = v_a_2500_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2481_);
lean_dec_ref(v_clears_2480_);
lean_dec(v_fs_2479_);
return v___x_2499_;
}
}
else
{
lean_object* v___x_2504_; 
lean_dec_ref(v_cont_2481_);
lean_dec_ref(v_clears_2480_);
lean_dec(v_fs_2479_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_b_2485_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_a_2507_, lean_object* v_fs_2508_, lean_object* v_clears_2509_, lean_object* v_cont_2510_, lean_object* v_e_2511_, lean_object* v___x_2512_, lean_object* v_g_2513_, lean_object* v___x_2514_, lean_object* v_pat_2515_, lean_object* v___y_2516_, lean_object* v_asFVar_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___y_2555_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2567_ = lean_box(0);
lean_inc_ref(v_e_2511_);
v___x_2568_ = l_Lean_Expr_mdata___override(v___x_2567_, v_e_2511_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_box(0);
v___x_2571_ = 0;
lean_inc(v___y_2516_);
v___x_2572_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2516_, v___x_2568_, v___x_2569_, v___x_2569_, v___x_2570_, v___x_2571_, v___x_2571_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref_known(v___x_2572_, 1);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc_ref(v_e_2511_);
v___x_2573_ = lean_apply_6(v_asFVar_2517_, v_e_2511_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, lean_box(0));
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref_known(v___x_2573_, 1);
v___x_2574_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2571_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2575_; 
lean_dec_ref_known(v___x_2574_, 1);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc_ref(v_e_2511_);
v___x_2575_ = lean_infer_type(v_e_2511_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = l_Lean_Meta_whnfD(v_a_2576_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = l_Lean_Expr_getAppFn(v_a_2578_);
if (lean_obj_tag(v___x_2579_) == 4)
{
lean_object* v_declName_2580_; lean_object* v___x_2581_; lean_object* v_env_2582_; lean_object* v___x_2583_; 
v_declName_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_declName_2580_);
lean_dec_ref_known(v___x_2579_, 2);
v___x_2581_ = lean_st_ref_get(v___y_2524_);
v_env_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc_ref(v_env_2582_);
lean_dec(v___x_2581_);
v___x_2583_ = l_Lean_Environment_find_x3f(v_env_2582_, v_declName_2580_, v___x_2571_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
v___x_2584_ = lean_box(0);
v___x_2585_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2511_, v_a_2578_, lean_box(0), v___x_2584_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2555_ = v___x_2585_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2586_; 
v_val_2586_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v___x_2583_, 1);
switch(lean_obj_tag(v_val_2586_))
{
case 4:
{
lean_object* v_val_2587_; uint8_t v_kind_2588_; 
lean_dec(v___y_2516_);
v_val_2587_ = lean_ctor_get(v_val_2586_, 0);
lean_inc_ref(v_val_2587_);
lean_dec_ref_known(v_val_2586_, 1);
v_kind_2588_ = lean_ctor_get_uint8(v_val_2587_, sizeof(void*)*1);
lean_dec_ref(v_val_2587_);
if (v_kind_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec(v_a_2578_);
v___x_2589_ = lean_box(0);
lean_inc(v_fs_2508_);
v___x_2590_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2571_, v_e_2511_, v___x_2512_, v_g_2513_, v___x_2514_, v_fs_2508_, v_pat_2515_, v___x_2589_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2555_ = v___x_2590_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_box(0);
lean_inc_ref(v_e_2511_);
v___x_2592_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2511_, v_a_2578_, lean_box(0), v___x_2591_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
lean_inc(v_fs_2508_);
v___x_2594_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2571_, v_e_2511_, v___x_2512_, v_g_2513_, v___x_2514_, v_fs_2508_, v_pat_2515_, v_a_2593_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2555_ = v___x_2594_;
goto v___jp_2554_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2595_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2592_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2592_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
case 5:
{
lean_object* v_val_2603_; lean_object* v_numParams_2604_; lean_object* v_ctors_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v_a_2578_);
lean_dec_ref(v___x_2514_);
lean_dec(v___x_2512_);
v_val_2603_ = lean_ctor_get(v_val_2586_, 0);
lean_inc_ref(v_val_2603_);
lean_dec_ref_known(v_val_2586_, 1);
v_numParams_2604_ = lean_ctor_get(v_val_2603_, 1);
lean_inc(v_numParams_2604_);
v_ctors_2605_ = lean_ctor_get(v_val_2603_, 4);
lean_inc(v_ctors_2605_);
lean_dec_ref(v_val_2603_);
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2607_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2515_);
v___x_2608_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2516_, v_numParams_2604_, v___x_2606_, v_ctors_2605_, v___x_2607_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v_numParams_2604_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v_fst_2610_; lean_object* v_snd_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v_fst_2610_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_fst_2610_);
v_snd_2611_ = lean_ctor_get(v_a_2609_, 1);
lean_inc(v_snd_2611_);
lean_dec(v_a_2609_);
v___x_2612_ = l_Lean_Expr_fvarId_x21(v_e_2511_);
lean_dec_ref(v_e_2511_);
v___x_2613_ = 1;
v___x_2614_ = l_Lean_MVarId_cases(v_g_2513_, v___x_2612_, v_fst_2610_, v___x_2613_, v___x_2569_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_fst_2527_ = v_snd_2611_;
v_snd_2528_ = v_a_2615_;
goto v___jp_2526_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_snd_2611_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2616_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_g_2513_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2624_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2608_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2608_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
default: 
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v_val_2586_);
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
v___x_2632_ = lean_box(0);
v___x_2633_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2511_, v_a_2578_, lean_box(0), v___x_2632_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2555_ = v___x_2633_;
goto v___jp_2554_;
}
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v___x_2579_);
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
v___x_2634_ = lean_box(0);
v___x_2635_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2511_, v_a_2578_, lean_box(0), v___x_2634_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
v___y_2555_ = v___x_2635_;
goto v___jp_2554_;
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2636_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2577_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2577_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2644_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2575_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2575_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2652_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2574_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2574_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2660_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2573_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2573_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v_asFVar_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v_pat_2515_);
lean_dec_ref(v___x_2514_);
lean_dec(v_g_2513_);
lean_dec(v___x_2512_);
lean_dec_ref(v_e_2511_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2668_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2572_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2572_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
v___jp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_array_get_size(v_snd_2528_);
v___x_2531_ = lean_nat_dec_lt(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_dec_ref(v_snd_2528_);
lean_dec(v_fst_2527_);
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_a_2507_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v_fst_2527_);
lean_ctor_set(v___x_2533_, 1, v_a_2507_);
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = lean_usize_of_nat(v___x_2530_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2508_, v_clears_2509_, v_cont_2510_, v_snd_2528_, v___x_2534_, v___x_2535_, v___x_2533_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec_ref(v_snd_2528_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2545_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_snd_2541_; lean_object* v___x_2543_; 
v_snd_2541_ = lean_ctor_get(v_a_2537_, 1);
lean_inc(v_snd_2541_);
lean_dec(v_a_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v_snd_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_snd_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_a_2546_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2536_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2536_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
v___jp_2554_:
{
if (lean_obj_tag(v___y_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v_fst_2557_; lean_object* v_snd_2558_; 
v_a_2556_ = lean_ctor_get(v___y_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___y_2555_, 1);
v_fst_2557_ = lean_ctor_get(v_a_2556_, 0);
lean_inc(v_fst_2557_);
v_snd_2558_ = lean_ctor_get(v_a_2556_, 1);
lean_inc(v_snd_2558_);
lean_dec(v_a_2556_);
v_fst_2527_ = v_fst_2557_;
v_snd_2528_ = v_snd_2558_;
goto v___jp_2526_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_cont_2510_);
lean_dec_ref(v_clears_2509_);
lean_dec(v_fs_2508_);
lean_dec(v_a_2507_);
v_a_2559_ = lean_ctor_get(v___y_2555_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___y_2555_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___y_2555_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___y_2555_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_a_2676_ = _args[0];
lean_object* v_fs_2677_ = _args[1];
lean_object* v_clears_2678_ = _args[2];
lean_object* v_cont_2679_ = _args[3];
lean_object* v_e_2680_ = _args[4];
lean_object* v___x_2681_ = _args[5];
lean_object* v_g_2682_ = _args[6];
lean_object* v___x_2683_ = _args[7];
lean_object* v_pat_2684_ = _args[8];
lean_object* v___y_2685_ = _args[9];
lean_object* v_asFVar_2686_ = _args[10];
lean_object* v_x_2687_ = _args[11];
lean_object* v___y_2688_ = _args[12];
lean_object* v___y_2689_ = _args[13];
lean_object* v___y_2690_ = _args[14];
lean_object* v___y_2691_ = _args[15];
lean_object* v___y_2692_ = _args[16];
lean_object* v___y_2693_ = _args[17];
lean_object* v___y_2694_ = _args[18];
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_a_2676_, v_fs_2677_, v_clears_2678_, v_cont_2679_, v_e_2680_, v___x_2681_, v_g_2682_, v___x_2683_, v_pat_2684_, v___y_2685_, v_asFVar_2686_, v_x_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v_x_2687_);
return v_res_2695_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2700_ = l_Lean_MessageData_ofFormat(v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2703_, lean_object* v___f_2704_, lean_object* v_e_2705_, lean_object* v_asFVar_2706_, lean_object* v_g_2707_, lean_object* v_fs_2708_, lean_object* v_cont_2709_, lean_object* v_clears_2710_, lean_object* v_a_2711_, lean_object* v___f_2712_, lean_object* v___f_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
switch(lean_obj_tag(v_pat_2703_))
{
case 1:
{
lean_object* v_a_2721_; 
lean_dec_ref(v___f_2713_);
lean_dec_ref(v___f_2712_);
v_a_2721_ = lean_ctor_get(v_pat_2703_, 1);
lean_inc(v_a_2721_);
if (lean_obj_tag(v_a_2721_) == 1)
{
lean_object* v_pre_2722_; 
v_pre_2722_ = lean_ctor_get(v_a_2721_, 0);
if (lean_obj_tag(v_pre_2722_) == 0)
{
lean_object* v_ref_2723_; lean_object* v_str_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_ref_2723_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2723_);
lean_dec_ref_known(v_pat_2703_, 2);
v_str_2724_ = lean_ctor_get(v_a_2721_, 1);
v___x_2725_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2726_ = lean_string_dec_eq(v_str_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2727_ = lean_apply_9(v___f_2704_, v_ref_2723_, v_a_2721_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2727_;
}
else
{
uint8_t v___x_2728_; lean_object* v___x_2729_; 
lean_inc(v_pre_2722_);
lean_dec_ref_known(v_a_2721_, 2);
lean_dec_ref(v___f_2704_);
v___x_2728_ = 0;
v___x_2729_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2728_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref_known(v___x_2729_, 1);
v___x_2730_ = lean_box(0);
lean_inc_ref(v_e_2705_);
v___x_2731_ = l_Lean_Expr_mdata___override(v___x_2730_, v_e_2705_);
v___x_2732_ = lean_box(0);
v___x_2733_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2723_, v___x_2731_, v___x_2732_, v___x_2732_, v_pre_2722_, v___x_2728_, v___x_2728_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2733_, 1);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
v___x_2734_ = lean_apply_6(v_asFVar_2706_, v_e_2705_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_Meta_substEq(v_g_2707_, v_a_2735_, v_fs_2708_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v_fst_2738_; lean_object* v_snd_2739_; lean_object* v___x_2740_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v_fst_2738_ = lean_ctor_get(v_a_2737_, 0);
lean_inc(v_fst_2738_);
v_snd_2739_ = lean_ctor_get(v_a_2737_, 1);
lean_inc(v_snd_2739_);
lean_dec(v_a_2737_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2740_ = lean_apply_11(v_cont_2709_, v_snd_2739_, v_fst_2738_, v_clears_2710_, v_a_2711_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2740_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
v_a_2741_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2736_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
v_a_2749_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2734_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2734_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
v_a_2757_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2733_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2733_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_ref_2723_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
v_a_2765_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2729_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2729_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
else
{
lean_object* v_ref_2773_; lean_object* v___x_2774_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
v_ref_2773_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2773_);
lean_dec_ref_known(v_pat_2703_, 2);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2774_ = lean_apply_9(v___f_2704_, v_ref_2773_, v_a_2721_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2774_;
}
}
else
{
lean_object* v_ref_2775_; lean_object* v___x_2776_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
v_ref_2775_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2775_);
lean_dec_ref_known(v_pat_2703_, 2);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2776_ = lean_apply_9(v___f_2704_, v_ref_2775_, v_a_2721_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2776_;
}
}
case 2:
{
lean_object* v_ref_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref(v___f_2713_);
lean_dec_ref(v___f_2712_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v___f_2704_);
v_ref_2777_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2777_);
lean_dec_ref_known(v_pat_2703_, 1);
v___x_2778_ = lean_box(0);
lean_inc_ref(v_e_2705_);
v___x_2779_ = l_Lean_Expr_mdata___override(v___x_2778_, v_e_2705_);
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_box(0);
v___x_2782_ = 0;
v___x_2783_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2777_, v___x_2779_, v___x_2780_, v___x_2780_, v___x_2781_, v___x_2782_, v___x_2782_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_dec_ref_known(v___x_2783_, 1);
if (lean_obj_tag(v_e_2705_) == 1)
{
lean_object* v_fvarId_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_fvarId_2784_ = lean_ctor_get(v_e_2705_, 0);
lean_inc(v_fvarId_2784_);
lean_dec_ref_known(v_e_2705_, 1);
v___x_2785_ = lean_array_push(v_clears_2710_, v_fvarId_2784_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2786_ = lean_apply_11(v_cont_2709_, v_g_2707_, v_fs_2708_, v___x_2785_, v_a_2711_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref(v_e_2705_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2787_ = lean_apply_11(v_cont_2709_, v_g_2707_, v_fs_2708_, v_clears_2710_, v_a_2711_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2787_;
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2788_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2783_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2783_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
case 4:
{
lean_object* v_ref_2796_; lean_object* v_a_2797_; lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; 
lean_dec_ref(v___f_2713_);
lean_dec_ref(v___f_2712_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v___f_2704_);
v_ref_2796_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2796_);
v_a_2797_ = lean_ctor_get(v_pat_2703_, 1);
lean_inc_ref(v_a_2797_);
v_a_2798_ = lean_ctor_get(v_pat_2703_, 2);
lean_inc(v_a_2798_);
lean_dec_ref_known(v_pat_2703_, 3);
v___x_2799_ = lean_box(0);
lean_inc_ref(v_e_2705_);
v___x_2800_ = l_Lean_Expr_mdata___override(v___x_2799_, v_e_2705_);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_box(0);
v___x_2803_ = 0;
v___x_2804_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2796_, v___x_2800_, v___x_2801_, v___x_2801_, v___x_2802_, v___x_2803_, v___x_2803_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref_known(v___x_2804_, 1);
v___x_2805_ = l_Lean_Elab_Term_elabType(v_a_2798_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___x_2827_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc_ref(v_e_2705_);
v___x_2827_ = lean_infer_type(v_e_2705_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_n(v_a_2828_, 2);
lean_dec_ref_known(v___x_2827_, 1);
lean_inc(v_a_2806_);
v___x_2829_ = l_Lean_Meta_isExprDefEq(v_a_2828_, v_a_2806_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; uint8_t v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = lean_unbox(v_a_2830_);
lean_dec(v_a_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2705_);
lean_inc(v_a_2806_);
v___x_2833_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2832_, v_a_2806_, v_a_2828_, v_e_2705_, v___x_2801_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_dec_ref_known(v___x_2833_, 1);
v___y_2808_ = v___y_2714_;
v___y_2809_ = v___y_2715_;
v___y_2810_ = v___y_2716_;
v___y_2811_ = v___y_2717_;
v___y_2812_ = v___y_2718_;
v___y_2813_ = v___y_2719_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_dec(v_a_2828_);
v___y_2808_ = v___y_2714_;
v___y_2809_ = v___y_2715_;
v___y_2810_ = v___y_2716_;
v___y_2811_ = v___y_2717_;
v___y_2812_ = v___y_2718_;
v___y_2813_ = v___y_2719_;
goto v___jp_2807_;
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2842_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2829_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2829_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2850_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2827_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2827_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
v___jp_2807_:
{
if (lean_obj_tag(v_e_2705_) == 1)
{
lean_object* v_fvarId_2814_; lean_object* v___x_2815_; 
v_fvarId_2814_ = lean_ctor_get(v_e_2705_, 0);
lean_inc(v_fvarId_2814_);
v___x_2815_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2707_, v_fvarId_2814_, v_a_2806_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2816_, v_fs_2708_, v_clears_2710_, v_e_2705_, v_a_2711_, v_a_2797_, v_cont_2709_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec_ref_known(v_e_2705_, 1);
return v___x_2817_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref_known(v_e_2705_, 1);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
v_a_2818_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2815_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2815_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v___x_2826_; 
lean_dec(v_a_2806_);
v___x_2826_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2707_, v_fs_2708_, v_clears_2710_, v_e_2705_, v_a_2711_, v_a_2797_, v_cont_2709_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec_ref(v_e_2705_);
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2858_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2805_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2805_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_e_2705_);
v_a_2866_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2804_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2804_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
case 0:
{
lean_object* v_ref_2874_; lean_object* v_a_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v___f_2713_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
lean_dec_ref(v___f_2704_);
v_ref_2874_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2874_);
v_a_2875_ = lean_ctor_get(v_pat_2703_, 1);
lean_inc_ref(v_a_2875_);
lean_dec_ref_known(v_pat_2703_, 2);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2876_ = lean_apply_9(v___f_2712_, v_ref_2874_, v_a_2875_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2876_;
}
case 6:
{
lean_object* v_a_2877_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
lean_dec_ref(v___f_2704_);
v_a_2877_ = lean_ctor_get(v_pat_2703_, 1);
if (lean_obj_tag(v_a_2877_) == 1)
{
lean_object* v_tail_2878_; 
v_tail_2878_ = lean_ctor_get(v_a_2877_, 1);
if (lean_obj_tag(v_tail_2878_) == 0)
{
lean_object* v_ref_2879_; lean_object* v_head_2880_; lean_object* v___x_2881_; 
lean_inc_ref(v_a_2877_);
lean_dec_ref(v___f_2713_);
v_ref_2879_ = lean_ctor_get(v_pat_2703_, 0);
lean_inc(v_ref_2879_);
lean_dec_ref_known(v_pat_2703_, 2);
v_head_2880_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_head_2880_);
lean_dec_ref_known(v_a_2877_, 2);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2881_ = lean_apply_9(v___f_2712_, v_ref_2879_, v_head_2880_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; 
lean_dec_ref(v___f_2712_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2882_ = lean_apply_8(v___f_2713_, v_pat_2703_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2882_;
}
}
else
{
lean_object* v___x_2883_; 
lean_dec_ref(v___f_2712_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2883_ = lean_apply_8(v___f_2713_, v_pat_2703_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2883_;
}
}
default: 
{
lean_object* v___x_2884_; 
lean_dec_ref(v___f_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_clears_2710_);
lean_dec_ref(v_cont_2709_);
lean_dec(v_fs_2708_);
lean_dec(v_g_2707_);
lean_dec_ref(v_asFVar_2706_);
lean_dec_ref(v_e_2705_);
lean_dec_ref(v___f_2704_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
v___x_2884_ = lean_apply_8(v___f_2713_, v_pat_2703_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, lean_box(0));
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2885_ = _args[0];
lean_object* v___f_2886_ = _args[1];
lean_object* v_e_2887_ = _args[2];
lean_object* v_asFVar_2888_ = _args[3];
lean_object* v_g_2889_ = _args[4];
lean_object* v_fs_2890_ = _args[5];
lean_object* v_cont_2891_ = _args[6];
lean_object* v_clears_2892_ = _args[7];
lean_object* v_a_2893_ = _args[8];
lean_object* v___f_2894_ = _args[9];
lean_object* v___f_2895_ = _args[10];
lean_object* v___y_2896_ = _args[11];
lean_object* v___y_2897_ = _args[12];
lean_object* v___y_2898_ = _args[13];
lean_object* v___y_2899_ = _args[14];
lean_object* v___y_2900_ = _args[15];
lean_object* v___y_2901_ = _args[16];
lean_object* v___y_2902_ = _args[17];
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2885_, v___f_2886_, v_e_2887_, v_asFVar_2888_, v_g_2889_, v_fs_2890_, v_cont_2891_, v_clears_2892_, v_a_2893_, v___f_2894_, v___f_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2904_, lean_object* v_fs_2905_, lean_object* v_clears_2906_, lean_object* v_e_2907_, lean_object* v_a_2908_, lean_object* v_pat_2909_, lean_object* v_cont_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_asFVar_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v_e_2921_; lean_object* v___f_2922_; lean_object* v___f_2923_; lean_object* v___y_2925_; lean_object* v_ref_2938_; 
v_asFVar_2918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2919_ = lean_box(1);
v___x_2920_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2905_, 3);
v_e_2921_ = l_Lean_Meta_FVarSubst_apply(v_fs_2905_, v_e_2907_);
lean_inc_n(v_a_2908_, 2);
lean_inc_ref_n(v_clears_2906_, 2);
lean_inc_n(v_g_2904_, 2);
lean_inc_ref_n(v_cont_2910_, 2);
lean_inc_ref_n(v_e_2921_, 2);
v___f_2922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2922_, 0, v_e_2921_);
lean_closure_set(v___f_2922_, 1, v_cont_2910_);
lean_closure_set(v___f_2922_, 2, v_g_2904_);
lean_closure_set(v___f_2922_, 3, v_fs_2905_);
lean_closure_set(v___f_2922_, 4, v_clears_2906_);
lean_closure_set(v___f_2922_, 5, v_a_2908_);
v___f_2923_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2923_, 0, v_e_2921_);
lean_closure_set(v___f_2923_, 1, v_g_2904_);
lean_closure_set(v___f_2923_, 2, v_fs_2905_);
lean_closure_set(v___f_2923_, 3, v_clears_2906_);
lean_closure_set(v___f_2923_, 4, v_a_2908_);
lean_closure_set(v___f_2923_, 5, v_cont_2910_);
v_ref_2938_ = lean_ctor_get(v_pat_2909_, 0);
lean_inc(v_ref_2938_);
v___y_2925_ = v_ref_2938_;
goto v___jp_2924_;
v___jp_2924_:
{
lean_object* v_toCold_2926_; lean_object* v_currRecDepth_2927_; lean_object* v_ref_2928_; uint16_t v_optionFlags_2929_; uint8_t v_suppressElabErrors_2930_; uint8_t v_checkDeprecated_2931_; uint8_t v_isRecordingDeps_2932_; lean_object* v___f_2933_; lean_object* v___y_2934_; lean_object* v_ref_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_toCold_2926_ = lean_ctor_get(v_a_2915_, 0);
v_currRecDepth_2927_ = lean_ctor_get(v_a_2915_, 1);
v_ref_2928_ = lean_ctor_get(v_a_2915_, 2);
v_optionFlags_2929_ = lean_ctor_get_uint16(v_a_2915_, sizeof(void*)*3);
v_suppressElabErrors_2930_ = lean_ctor_get_uint8(v_a_2915_, sizeof(void*)*3 + 2);
v_checkDeprecated_2931_ = lean_ctor_get_uint8(v_a_2915_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2932_ = lean_ctor_get_uint8(v_a_2915_, sizeof(void*)*3 + 4);
lean_inc(v___y_2925_);
lean_inc_ref(v_pat_2909_);
lean_inc_n(v_g_2904_, 2);
lean_inc_ref(v_e_2921_);
lean_inc_ref(v_cont_2910_);
lean_inc_ref(v_clears_2906_);
lean_inc(v_fs_2905_);
lean_inc(v_a_2908_);
v___f_2933_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2933_, 0, v_a_2908_);
lean_closure_set(v___f_2933_, 1, v_fs_2905_);
lean_closure_set(v___f_2933_, 2, v_clears_2906_);
lean_closure_set(v___f_2933_, 3, v_cont_2910_);
lean_closure_set(v___f_2933_, 4, v_e_2921_);
lean_closure_set(v___f_2933_, 5, v___x_2919_);
lean_closure_set(v___f_2933_, 6, v_g_2904_);
lean_closure_set(v___f_2933_, 7, v___x_2920_);
lean_closure_set(v___f_2933_, 8, v_pat_2909_);
lean_closure_set(v___f_2933_, 9, v___y_2925_);
lean_closure_set(v___f_2933_, 10, v_asFVar_2918_);
v___y_2934_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2934_, 0, v_pat_2909_);
lean_closure_set(v___y_2934_, 1, v___f_2922_);
lean_closure_set(v___y_2934_, 2, v_e_2921_);
lean_closure_set(v___y_2934_, 3, v_asFVar_2918_);
lean_closure_set(v___y_2934_, 4, v_g_2904_);
lean_closure_set(v___y_2934_, 5, v_fs_2905_);
lean_closure_set(v___y_2934_, 6, v_cont_2910_);
lean_closure_set(v___y_2934_, 7, v_clears_2906_);
lean_closure_set(v___y_2934_, 8, v_a_2908_);
lean_closure_set(v___y_2934_, 9, v___f_2923_);
lean_closure_set(v___y_2934_, 10, v___f_2933_);
v_ref_2935_ = l_Lean_replaceRef(v___y_2925_, v_ref_2928_);
lean_dec(v___y_2925_);
lean_inc(v_currRecDepth_2927_);
lean_inc_ref(v_toCold_2926_);
v___x_2936_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2936_, 0, v_toCold_2926_);
lean_ctor_set(v___x_2936_, 1, v_currRecDepth_2927_);
lean_ctor_set(v___x_2936_, 2, v_ref_2935_);
lean_ctor_set_uint16(v___x_2936_, sizeof(void*)*3, v_optionFlags_2929_);
lean_ctor_set_uint8(v___x_2936_, sizeof(void*)*3 + 2, v_suppressElabErrors_2930_);
lean_ctor_set_uint8(v___x_2936_, sizeof(void*)*3 + 3, v_checkDeprecated_2931_);
lean_ctor_set_uint8(v___x_2936_, sizeof(void*)*3 + 4, v_isRecordingDeps_2932_);
v___x_2937_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2904_, v___y_2934_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v___x_2936_, v_a_2916_);
lean_dec_ref_known(v___x_2936_, 3);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2939_, lean_object* v_fs_2940_, lean_object* v_clears_2941_, lean_object* v_a_2942_, lean_object* v_pats_2943_, lean_object* v_cont_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
if (lean_obj_tag(v_pats_2943_) == 0)
{
lean_object* v___x_2952_; 
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc(v_a_2946_);
lean_inc_ref(v_a_2945_);
v___x_2952_ = lean_apply_11(v_cont_2944_, v_g_2939_, v_fs_2940_, v_clears_2941_, v_a_2942_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, lean_box(0));
return v___x_2952_;
}
else
{
lean_object* v_head_2953_; lean_object* v_tail_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___f_2957_; lean_object* v___x_2958_; 
v_head_2953_ = lean_ctor_get(v_pats_2943_, 0);
lean_inc(v_head_2953_);
v_tail_2954_ = lean_ctor_get(v_pats_2943_, 1);
lean_inc(v_tail_2954_);
lean_dec_ref_known(v_pats_2943_, 2);
v_fst_2955_ = lean_ctor_get(v_head_2953_, 0);
lean_inc(v_fst_2955_);
v_snd_2956_ = lean_ctor_get(v_head_2953_, 1);
lean_inc(v_snd_2956_);
lean_dec(v_head_2953_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2957_, 0, v_tail_2954_);
lean_closure_set(v___f_2957_, 1, v_cont_2944_);
v___x_2958_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2939_, v_fs_2940_, v_clears_2941_, v_snd_2956_, v_a_2942_, v_fst_2955_, v___f_2957_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_snd_2956_);
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2959_, lean_object* v_cont_2960_, lean_object* v_g_2961_, lean_object* v_fs_2962_, lean_object* v_clears_2963_, lean_object* v_a_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2961_, v_fs_2962_, v_clears_2963_, v_a_2964_, v_tail_2959_, v_cont_2960_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2973_, lean_object* v_fs_2974_, lean_object* v_clears_2975_, lean_object* v_a_2976_, lean_object* v_pats_2977_, lean_object* v_cont_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2973_, v_fs_2974_, v_clears_2975_, v_a_2976_, v_pats_2977_, v_cont_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_2987_, lean_object* v_clears_2988_, lean_object* v_cont_2989_, lean_object* v_as_2990_, lean_object* v_i_2991_, lean_object* v_stop_2992_, lean_object* v_b_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
size_t v_i_boxed_3001_; size_t v_stop_boxed_3002_; lean_object* v_res_3003_; 
v_i_boxed_3001_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_stop_boxed_3002_ = lean_unbox_usize(v_stop_2992_);
lean_dec(v_stop_2992_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2987_, v_clears_2988_, v_cont_2989_, v_as_2990_, v_i_boxed_3001_, v_stop_boxed_3002_, v_b_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v_as_2990_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3004_, lean_object* v_fs_3005_, lean_object* v_clears_3006_, lean_object* v_e_3007_, lean_object* v_a_3008_, lean_object* v_pat_3009_, lean_object* v_cont_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3004_, v_fs_3005_, v_clears_3006_, v_e_3007_, v_a_3008_, v_pat_3009_, v_cont_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec_ref(v_e_3007_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_3019_, lean_object* v_clears_3020_, lean_object* v_cont_3021_, lean_object* v_a_3022_, lean_object* v_goal_3023_, lean_object* v_ctorName_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3019_, v_clears_3020_, v_cont_3021_, v_a_3022_, v_goal_3023_, v_ctorName_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_ctorName_3024_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3034_, lean_object* v_g_3035_, lean_object* v_fs_3036_, lean_object* v_clears_3037_, lean_object* v_a_3038_, lean_object* v_pats_3039_, lean_object* v_cont_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3035_, v_fs_3036_, v_clears_3037_, v_a_3038_, v_pats_3039_, v_cont_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_g_3050_, lean_object* v_fs_3051_, lean_object* v_clears_3052_, lean_object* v_a_3053_, lean_object* v_pats_3054_, lean_object* v_cont_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3049_, v_g_3050_, v_fs_3051_, v_clears_3052_, v_a_3053_, v_pats_3054_, v_cont_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3064_, lean_object* v_fs_3065_, lean_object* v_clears_3066_, lean_object* v_cont_3067_, lean_object* v_a_3068_, lean_object* v_goal_3069_, lean_object* v_ctorName_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3065_, v_clears_3066_, v_cont_3067_, v_a_3068_, v_goal_3069_, v_ctorName_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_fs_3081_, lean_object* v_clears_3082_, lean_object* v_cont_3083_, lean_object* v_a_3084_, lean_object* v_goal_3085_, lean_object* v_ctorName_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3080_, v_fs_3081_, v_clears_3082_, v_cont_3083_, v_a_3084_, v_goal_3085_, v_ctorName_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_ctorName_3086_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3096_, lean_object* v_mvarId_3097_, lean_object* v_x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3097_, v_x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3107_, lean_object* v_mvarId_3108_, lean_object* v_x_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3107_, v_mvarId_3108_, v_x_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3118_, lean_object* v_g_3119_, lean_object* v_fs_3120_, lean_object* v_clears_3121_, lean_object* v_e_3122_, lean_object* v_a_3123_, lean_object* v_pat_3124_, lean_object* v_cont_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3119_, v_fs_3120_, v_clears_3121_, v_e_3122_, v_a_3123_, v_pat_3124_, v_cont_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_g_3135_, lean_object* v_fs_3136_, lean_object* v_clears_3137_, lean_object* v_e_3138_, lean_object* v_a_3139_, lean_object* v_pat_3140_, lean_object* v_cont_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3134_, v_g_3135_, v_fs_3136_, v_clears_3137_, v_e_3138_, v_a_3139_, v_pat_3140_, v_cont_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec_ref(v_e_3138_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3150_, lean_object* v_fs_3151_, lean_object* v_clears_3152_, lean_object* v_cont_3153_, lean_object* v_as_3154_, size_t v_i_3155_, size_t v_stop_3156_, lean_object* v_b_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3151_, v_clears_3152_, v_cont_3153_, v_as_3154_, v_i_3155_, v_stop_3156_, v_b_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_fs_3167_, lean_object* v_clears_3168_, lean_object* v_cont_3169_, lean_object* v_as_3170_, lean_object* v_i_3171_, lean_object* v_stop_3172_, lean_object* v_b_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
size_t v_i_boxed_3181_; size_t v_stop_boxed_3182_; lean_object* v_res_3183_; 
v_i_boxed_3181_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_stop_boxed_3182_ = lean_unbox_usize(v_stop_3172_);
lean_dec(v_stop_3172_);
v_res_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3166_, v_fs_3167_, v_clears_3168_, v_cont_3169_, v_as_3170_, v_i_boxed_3181_, v_stop_boxed_3182_, v_b_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_as_3170_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3184_, lean_object* v_val_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3184_, v_val_3185_, v___y_3189_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3194_, lean_object* v_val_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3194_, v_val_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3204_, lean_object* v_msg_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_msg_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3214_, v_msg_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3225_, v_x_3226_, v_x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3229_, lean_object* v_macroStack_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3229_, v_macroStack_3230_, v___y_3235_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3239_, lean_object* v_macroStack_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3239_, v_macroStack_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3249_, lean_object* v_x_3250_, size_t v_x_3251_, size_t v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3250_, v_x_3251_, v_x_3252_, v_x_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3256_, lean_object* v_x_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
size_t v_x_20569__boxed_3262_; size_t v_x_20570__boxed_3263_; lean_object* v_res_3264_; 
v_x_20569__boxed_3262_ = lean_unbox_usize(v_x_3258_);
lean_dec(v_x_3258_);
v_x_20570__boxed_3263_ = lean_unbox_usize(v_x_3259_);
lean_dec(v_x_3259_);
v_res_3264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3256_, v_x_3257_, v_x_20569__boxed_3262_, v_x_20570__boxed_3263_, v_x_3260_, v_x_3261_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3265_, lean_object* v_n_3266_, lean_object* v_k_3267_, lean_object* v_v_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3266_, v_k_3267_, v_v_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3270_, size_t v_depth_3271_, lean_object* v_keys_3272_, lean_object* v_vals_3273_, lean_object* v_heq_3274_, lean_object* v_i_3275_, lean_object* v_entries_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3271_, v_keys_3272_, v_vals_3273_, v_i_3275_, v_entries_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_depth_3279_, lean_object* v_keys_3280_, lean_object* v_vals_3281_, lean_object* v_heq_3282_, lean_object* v_i_3283_, lean_object* v_entries_3284_){
_start:
{
size_t v_depth_boxed_3285_; lean_object* v_res_3286_; 
v_depth_boxed_3285_ = lean_unbox_usize(v_depth_3279_);
lean_dec(v_depth_3279_);
v_res_3286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3278_, v_depth_boxed_3285_, v_keys_3280_, v_vals_3281_, v_heq_3282_, v_i_3283_, v_entries_3284_);
lean_dec_ref(v_vals_3281_);
lean_dec_ref(v_keys_3280_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3288_, v_x_3289_, v_x_3290_, v_x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3293_, lean_object* v_as_3294_, size_t v_i_3295_, size_t v_stop_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_usize_dec_eq(v_i_3295_, v_stop_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = lean_array_uget_borrowed(v_as_3294_, v_i_3295_);
v___x_3299_ = l_Lean_instBEqFVarId_beq(v_a_3293_, v___x_3298_);
if (v___x_3299_ == 0)
{
size_t v___x_3300_; size_t v___x_3301_; 
v___x_3300_ = ((size_t)1ULL);
v___x_3301_ = lean_usize_add(v_i_3295_, v___x_3300_);
v_i_3295_ = v___x_3301_;
goto _start;
}
else
{
return v___x_3299_;
}
}
else
{
uint8_t v___x_3303_; 
v___x_3303_ = 0;
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3304_, lean_object* v_as_3305_, lean_object* v_i_3306_, lean_object* v_stop_3307_){
_start:
{
size_t v_i_boxed_3308_; size_t v_stop_boxed_3309_; uint8_t v_res_3310_; lean_object* v_r_3311_; 
v_i_boxed_3308_ = lean_unbox_usize(v_i_3306_);
lean_dec(v_i_3306_);
v_stop_boxed_3309_ = lean_unbox_usize(v_stop_3307_);
lean_dec(v_stop_3307_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3304_, v_as_3305_, v_i_boxed_3308_, v_stop_boxed_3309_);
lean_dec_ref(v_as_3305_);
lean_dec(v_a_3304_);
v_r_3311_ = lean_box(v_res_3310_);
return v_r_3311_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = lean_array_get_size(v_as_3312_);
v___x_3316_ = lean_nat_dec_lt(v___x_3314_, v___x_3315_);
if (v___x_3316_ == 0)
{
return v___x_3316_;
}
else
{
size_t v___x_3317_; size_t v___x_3318_; uint8_t v___x_3319_; 
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = lean_usize_of_nat(v___x_3315_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3313_, v_as_3312_, v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3320_, lean_object* v_a_3321_){
_start:
{
uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_res_3322_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_as_3320_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3324_, v___y_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec(v_snd_3327_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3331_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = 0;
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3333_){
_start:
{
uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3333_);
lean_dec(v_x_3333_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_unsigned_to_nat(16u);
v___x_3339_ = lean_mk_array(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v___x_3340_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3343_, size_t v_sz_3344_, size_t v_i_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_lt(v_i_3345_, v_sz_3344_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3346_);
return v___x_3350_;
}
else
{
lean_object* v_snd_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3483_; 
v_snd_3351_ = lean_ctor_get(v_b_3346_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_b_3346_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_b_3346_, 0);
lean_dec(v_unused_3484_);
v___x_3353_ = v_b_3346_;
v_isShared_3354_ = v_isSharedCheck_3483_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_snd_3351_);
lean_dec(v_b_3346_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3483_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v_a_3357_; lean_object* v_a_3364_; 
v___x_3355_ = lean_box(0);
v_a_3364_ = lean_array_uget_borrowed(v_as_3343_, v_i_3345_);
if (lean_obj_tag(v_a_3364_) == 0)
{
v_a_3357_ = v_snd_3351_;
goto v___jp_3356_;
}
else
{
lean_object* v_val_3365_; uint8_t v_a_3367_; lean_object* v___f_3370_; lean_object* v___f_3371_; 
v_val_3365_ = lean_ctor_get(v_a_3364_, 0);
v___f_3370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3351_);
v___f_3371_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3371_, 0, v_snd_3351_);
if (lean_obj_tag(v_val_3365_) == 0)
{
lean_object* v_type_3372_; lean_object* v___x_3373_; uint8_t v_fst_3375_; lean_object* v_mctx_3376_; lean_object* v___y_3392_; lean_object* v_mctx_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v_type_3372_ = lean_ctor_get(v_val_3365_, 3);
v___x_3373_ = lean_st_ref_get(v___y_3347_);
v_mctx_3397_ = lean_ctor_get(v___x_3373_, 0);
lean_inc_ref_n(v_mctx_3397_, 2);
lean_dec(v___x_3373_);
v___x_3398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_mctx_3397_);
v___x_3400_ = l_Lean_Expr_hasFVar(v_type_3372_);
if (v___x_3400_ == 0)
{
uint8_t v___x_3401_; 
v___x_3401_ = l_Lean_Expr_hasMVar(v_type_3372_);
if (v___x_3401_ == 0)
{
lean_dec_ref_known(v___x_3399_, 2);
lean_dec_ref(v___f_3371_);
v_fst_3375_ = v___x_3401_;
v_mctx_3376_ = v_mctx_3397_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3402_; 
lean_dec_ref(v_mctx_3397_);
lean_inc_ref(v_type_3372_);
v___x_3402_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3372_, v___x_3399_);
v___y_3392_ = v___x_3402_;
goto v___jp_3391_;
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_mctx_3397_);
lean_inc_ref(v_type_3372_);
v___x_3403_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3372_, v___x_3399_);
v___y_3392_ = v___x_3403_;
goto v___jp_3391_;
}
v___jp_3374_:
{
lean_object* v___x_3377_; lean_object* v_cache_3378_; lean_object* v_zetaDeltaFVarIds_3379_; lean_object* v_postponed_3380_; lean_object* v_diag_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3389_; 
v___x_3377_ = lean_st_ref_take(v___y_3347_);
v_cache_3378_ = lean_ctor_get(v___x_3377_, 1);
v_zetaDeltaFVarIds_3379_ = lean_ctor_get(v___x_3377_, 2);
v_postponed_3380_ = lean_ctor_get(v___x_3377_, 3);
v_diag_3381_ = lean_ctor_get(v___x_3377_, 4);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v___x_3377_, 0);
lean_dec(v_unused_3390_);
v___x_3383_ = v___x_3377_;
v_isShared_3384_ = v_isSharedCheck_3389_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_diag_3381_);
lean_inc(v_postponed_3380_);
lean_inc(v_zetaDeltaFVarIds_3379_);
lean_inc(v_cache_3378_);
lean_dec(v___x_3377_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3389_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v_mctx_3376_);
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_mctx_3376_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_cache_3378_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_zetaDeltaFVarIds_3379_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_postponed_3380_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v_diag_3381_);
v___x_3386_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_st_ref_put(v___y_3347_, v___x_3386_);
v_a_3367_ = v_fst_3375_;
goto v___jp_3366_;
}
}
}
v___jp_3391_:
{
lean_object* v_snd_3393_; lean_object* v_fst_3394_; lean_object* v_mctx_3395_; uint8_t v___x_3396_; 
v_snd_3393_ = lean_ctor_get(v___y_3392_, 1);
lean_inc(v_snd_3393_);
v_fst_3394_ = lean_ctor_get(v___y_3392_, 0);
lean_inc(v_fst_3394_);
lean_dec_ref(v___y_3392_);
v_mctx_3395_ = lean_ctor_get(v_snd_3393_, 1);
lean_inc_ref(v_mctx_3395_);
lean_dec(v_snd_3393_);
v___x_3396_ = lean_unbox(v_fst_3394_);
lean_dec(v_fst_3394_);
v_fst_3375_ = v___x_3396_;
v_mctx_3376_ = v_mctx_3395_;
goto v___jp_3374_;
}
}
else
{
uint8_t v_nondep_3404_; 
v_nondep_3404_ = lean_ctor_get_uint8(v_val_3365_, sizeof(void*)*5);
if (v_nondep_3404_ == 0)
{
lean_object* v_type_3405_; lean_object* v_value_3406_; lean_object* v___x_3407_; uint8_t v_fst_3409_; lean_object* v_snd_3410_; lean_object* v___y_3427_; lean_object* v_snd_3432_; lean_object* v___y_3438_; lean_object* v_mctx_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_type_3405_ = lean_ctor_get(v_val_3365_, 3);
v_value_3406_ = lean_ctor_get(v_val_3365_, 4);
v___x_3407_ = lean_st_ref_get(v___y_3347_);
v_mctx_3444_ = lean_ctor_get(v___x_3407_, 0);
lean_inc_ref(v_mctx_3444_);
lean_dec(v___x_3407_);
v___x_3445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v_mctx_3444_);
v___x_3447_ = l_Lean_Expr_hasFVar(v_type_3405_);
if (v___x_3447_ == 0)
{
uint8_t v___x_3448_; 
v___x_3448_ = l_Lean_Expr_hasMVar(v_type_3405_);
if (v___x_3448_ == 0)
{
v_snd_3432_ = v___x_3446_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3449_; 
lean_inc_ref(v_type_3405_);
lean_inc_ref(v___f_3371_);
v___x_3449_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3405_, v___x_3446_);
v___y_3438_ = v___x_3449_;
goto v___jp_3437_;
}
}
else
{
lean_object* v___x_3450_; 
lean_inc_ref(v_type_3405_);
lean_inc_ref(v___f_3371_);
v___x_3450_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3405_, v___x_3446_);
v___y_3438_ = v___x_3450_;
goto v___jp_3437_;
}
v___jp_3408_:
{
lean_object* v_mctx_3411_; lean_object* v___x_3412_; lean_object* v_cache_3413_; lean_object* v_zetaDeltaFVarIds_3414_; lean_object* v_postponed_3415_; lean_object* v_diag_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_mctx_3411_ = lean_ctor_get(v_snd_3410_, 1);
lean_inc_ref(v_mctx_3411_);
lean_dec_ref(v_snd_3410_);
v___x_3412_ = lean_st_ref_take(v___y_3347_);
v_cache_3413_ = lean_ctor_get(v___x_3412_, 1);
v_zetaDeltaFVarIds_3414_ = lean_ctor_get(v___x_3412_, 2);
v_postponed_3415_ = lean_ctor_get(v___x_3412_, 3);
v_diag_3416_ = lean_ctor_get(v___x_3412_, 4);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3412_, 0);
lean_dec(v_unused_3425_);
v___x_3418_ = v___x_3412_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_diag_3416_);
lean_inc(v_postponed_3415_);
lean_inc(v_zetaDeltaFVarIds_3414_);
lean_inc(v_cache_3413_);
lean_dec(v___x_3412_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_mctx_3411_);
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_mctx_3411_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_cache_3413_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_zetaDeltaFVarIds_3414_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_postponed_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_diag_3416_);
v___x_3421_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_st_ref_put(v___y_3347_, v___x_3421_);
v_a_3367_ = v_fst_3409_;
goto v___jp_3366_;
}
}
}
v___jp_3426_:
{
lean_object* v_fst_3428_; lean_object* v_snd_3429_; uint8_t v___x_3430_; 
v_fst_3428_ = lean_ctor_get(v___y_3427_, 0);
lean_inc(v_fst_3428_);
v_snd_3429_ = lean_ctor_get(v___y_3427_, 1);
lean_inc(v_snd_3429_);
lean_dec_ref(v___y_3427_);
v___x_3430_ = lean_unbox(v_fst_3428_);
lean_dec(v_fst_3428_);
v_fst_3409_ = v___x_3430_;
v_snd_3410_ = v_snd_3429_;
goto v___jp_3408_;
}
v___jp_3431_:
{
uint8_t v___x_3433_; 
v___x_3433_ = l_Lean_Expr_hasFVar(v_value_3406_);
if (v___x_3433_ == 0)
{
uint8_t v___x_3434_; 
v___x_3434_ = l_Lean_Expr_hasMVar(v_value_3406_);
if (v___x_3434_ == 0)
{
lean_dec_ref(v___f_3371_);
v_fst_3409_ = v___x_3434_;
v_snd_3410_ = v_snd_3432_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3435_; 
lean_inc_ref(v_value_3406_);
v___x_3435_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_value_3406_, v_snd_3432_);
v___y_3427_ = v___x_3435_;
goto v___jp_3426_;
}
}
else
{
lean_object* v___x_3436_; 
lean_inc_ref(v_value_3406_);
v___x_3436_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_value_3406_, v_snd_3432_);
v___y_3427_ = v___x_3436_;
goto v___jp_3426_;
}
}
v___jp_3437_:
{
lean_object* v_fst_3439_; uint8_t v___x_3440_; 
v_fst_3439_ = lean_ctor_get(v___y_3438_, 0);
v___x_3440_ = lean_unbox(v_fst_3439_);
if (v___x_3440_ == 0)
{
lean_object* v_snd_3441_; 
v_snd_3441_ = lean_ctor_get(v___y_3438_, 1);
lean_inc(v_snd_3441_);
lean_dec_ref(v___y_3438_);
v_snd_3432_ = v_snd_3441_;
goto v___jp_3431_;
}
else
{
lean_object* v_snd_3442_; uint8_t v___x_3443_; 
lean_inc(v_fst_3439_);
lean_dec_ref(v___f_3371_);
v_snd_3442_ = lean_ctor_get(v___y_3438_, 1);
lean_inc(v_snd_3442_);
lean_dec_ref(v___y_3438_);
v___x_3443_ = lean_unbox(v_fst_3439_);
lean_dec(v_fst_3439_);
v_fst_3409_ = v___x_3443_;
v_snd_3410_ = v_snd_3442_;
goto v___jp_3408_;
}
}
}
else
{
lean_object* v_type_3451_; lean_object* v___x_3452_; uint8_t v_fst_3454_; lean_object* v_mctx_3455_; lean_object* v___y_3471_; lean_object* v_mctx_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v_type_3451_ = lean_ctor_get(v_val_3365_, 3);
v___x_3452_ = lean_st_ref_get(v___y_3347_);
v_mctx_3476_ = lean_ctor_get(v___x_3452_, 0);
lean_inc_ref_n(v_mctx_3476_, 2);
lean_dec(v___x_3452_);
v___x_3477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v_mctx_3476_);
v___x_3479_ = l_Lean_Expr_hasFVar(v_type_3451_);
if (v___x_3479_ == 0)
{
uint8_t v___x_3480_; 
v___x_3480_ = l_Lean_Expr_hasMVar(v_type_3451_);
if (v___x_3480_ == 0)
{
lean_dec_ref_known(v___x_3478_, 2);
lean_dec_ref(v___f_3371_);
v_fst_3454_ = v___x_3480_;
v_mctx_3455_ = v_mctx_3476_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3481_; 
lean_dec_ref(v_mctx_3476_);
lean_inc_ref(v_type_3451_);
v___x_3481_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3451_, v___x_3478_);
v___y_3471_ = v___x_3481_;
goto v___jp_3470_;
}
}
else
{
lean_object* v___x_3482_; 
lean_dec_ref(v_mctx_3476_);
lean_inc_ref(v_type_3451_);
v___x_3482_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3371_, v___f_3370_, v_type_3451_, v___x_3478_);
v___y_3471_ = v___x_3482_;
goto v___jp_3470_;
}
v___jp_3453_:
{
lean_object* v___x_3456_; lean_object* v_cache_3457_; lean_object* v_zetaDeltaFVarIds_3458_; lean_object* v_postponed_3459_; lean_object* v_diag_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3468_; 
v___x_3456_ = lean_st_ref_take(v___y_3347_);
v_cache_3457_ = lean_ctor_get(v___x_3456_, 1);
v_zetaDeltaFVarIds_3458_ = lean_ctor_get(v___x_3456_, 2);
v_postponed_3459_ = lean_ctor_get(v___x_3456_, 3);
v_diag_3460_ = lean_ctor_get(v___x_3456_, 4);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3469_);
v___x_3462_ = v___x_3456_;
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_diag_3460_);
lean_inc(v_postponed_3459_);
lean_inc(v_zetaDeltaFVarIds_3458_);
lean_inc(v_cache_3457_);
lean_dec(v___x_3456_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v_mctx_3455_);
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_mctx_3455_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_cache_3457_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_zetaDeltaFVarIds_3458_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_postponed_3459_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_diag_3460_);
v___x_3465_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_st_ref_put(v___y_3347_, v___x_3465_);
v_a_3367_ = v_fst_3454_;
goto v___jp_3366_;
}
}
}
v___jp_3470_:
{
lean_object* v_snd_3472_; lean_object* v_fst_3473_; lean_object* v_mctx_3474_; uint8_t v___x_3475_; 
v_snd_3472_ = lean_ctor_get(v___y_3471_, 1);
lean_inc(v_snd_3472_);
v_fst_3473_ = lean_ctor_get(v___y_3471_, 0);
lean_inc(v_fst_3473_);
lean_dec_ref(v___y_3471_);
v_mctx_3474_ = lean_ctor_get(v_snd_3472_, 1);
lean_inc_ref(v_mctx_3474_);
lean_dec(v_snd_3472_);
v___x_3475_ = lean_unbox(v_fst_3473_);
lean_dec(v_fst_3473_);
v_fst_3454_ = v___x_3475_;
v_mctx_3455_ = v_mctx_3474_;
goto v___jp_3453_;
}
}
}
v___jp_3366_:
{
if (v_a_3367_ == 0)
{
v_a_3357_ = v_snd_3351_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = l_Lean_LocalDecl_fvarId(v_val_3365_);
v___x_3369_ = lean_array_push(v_snd_3351_, v___x_3368_);
v_a_3357_ = v___x_3369_;
goto v___jp_3356_;
}
}
}
v___jp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v_a_3357_);
lean_ctor_set(v___x_3353_, 0, v___x_3355_);
v___x_3359_ = v___x_3353_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_a_3357_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
size_t v___x_3360_; size_t v___x_3361_; 
v___x_3360_ = ((size_t)1ULL);
v___x_3361_ = lean_usize_add(v_i_3345_, v___x_3360_);
v_i_3345_ = v___x_3361_;
v_b_3346_ = v___x_3359_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3485_, lean_object* v_sz_3486_, lean_object* v_i_3487_, lean_object* v_b_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
size_t v_sz_boxed_3491_; size_t v_i_boxed_3492_; lean_object* v_res_3493_; 
v_sz_boxed_3491_ = lean_unbox_usize(v_sz_3486_);
lean_dec(v_sz_3486_);
v_i_boxed_3492_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3485_, v_sz_boxed_3491_, v_i_boxed_3492_, v_b_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v_as_3485_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3494_, size_t v_sz_3495_, size_t v_i_3496_, lean_object* v_b_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_usize_dec_lt(v_i_3496_, v_sz_3495_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_b_3497_);
return v___x_3504_;
}
else
{
lean_object* v_snd_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3637_; 
v_snd_3505_ = lean_ctor_get(v_b_3497_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_b_3497_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v_b_3497_, 0);
lean_dec(v_unused_3638_);
v___x_3507_ = v_b_3497_;
v_isShared_3508_ = v_isSharedCheck_3637_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_snd_3505_);
lean_dec(v_b_3497_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3637_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v_a_3511_; lean_object* v_a_3518_; 
v___x_3509_ = lean_box(0);
v_a_3518_ = lean_array_uget_borrowed(v_as_3494_, v_i_3496_);
if (lean_obj_tag(v_a_3518_) == 0)
{
v_a_3511_ = v_snd_3505_;
goto v___jp_3510_;
}
else
{
lean_object* v_val_3519_; uint8_t v_a_3521_; lean_object* v___f_3524_; lean_object* v___f_3525_; 
v_val_3519_ = lean_ctor_get(v_a_3518_, 0);
v___f_3524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3505_);
v___f_3525_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3525_, 0, v_snd_3505_);
if (lean_obj_tag(v_val_3519_) == 0)
{
lean_object* v_type_3526_; lean_object* v___x_3527_; uint8_t v_fst_3529_; lean_object* v_mctx_3530_; lean_object* v___y_3546_; lean_object* v_mctx_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_type_3526_ = lean_ctor_get(v_val_3519_, 3);
v___x_3527_ = lean_st_ref_get(v___y_3499_);
v_mctx_3551_ = lean_ctor_get(v___x_3527_, 0);
lean_inc_ref_n(v_mctx_3551_, 2);
lean_dec(v___x_3527_);
v___x_3552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
lean_ctor_set(v___x_3553_, 1, v_mctx_3551_);
v___x_3554_ = l_Lean_Expr_hasFVar(v_type_3526_);
if (v___x_3554_ == 0)
{
uint8_t v___x_3555_; 
v___x_3555_ = l_Lean_Expr_hasMVar(v_type_3526_);
if (v___x_3555_ == 0)
{
lean_dec_ref_known(v___x_3553_, 2);
lean_dec_ref(v___f_3525_);
v_fst_3529_ = v___x_3555_;
v_mctx_3530_ = v_mctx_3551_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3556_; 
lean_dec_ref(v_mctx_3551_);
lean_inc_ref(v_type_3526_);
v___x_3556_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3526_, v___x_3553_);
v___y_3546_ = v___x_3556_;
goto v___jp_3545_;
}
}
else
{
lean_object* v___x_3557_; 
lean_dec_ref(v_mctx_3551_);
lean_inc_ref(v_type_3526_);
v___x_3557_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3526_, v___x_3553_);
v___y_3546_ = v___x_3557_;
goto v___jp_3545_;
}
v___jp_3528_:
{
lean_object* v___x_3531_; lean_object* v_cache_3532_; lean_object* v_zetaDeltaFVarIds_3533_; lean_object* v_postponed_3534_; lean_object* v_diag_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v___x_3531_ = lean_st_ref_take(v___y_3499_);
v_cache_3532_ = lean_ctor_get(v___x_3531_, 1);
v_zetaDeltaFVarIds_3533_ = lean_ctor_get(v___x_3531_, 2);
v_postponed_3534_ = lean_ctor_get(v___x_3531_, 3);
v_diag_3535_ = lean_ctor_get(v___x_3531_, 4);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3531_, 0);
lean_dec(v_unused_3544_);
v___x_3537_ = v___x_3531_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_diag_3535_);
lean_inc(v_postponed_3534_);
lean_inc(v_zetaDeltaFVarIds_3533_);
lean_inc(v_cache_3532_);
lean_dec(v___x_3531_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_mctx_3530_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_mctx_3530_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_cache_3532_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_zetaDeltaFVarIds_3533_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_postponed_3534_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_diag_3535_);
v___x_3540_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_st_ref_put(v___y_3499_, v___x_3540_);
v_a_3521_ = v_fst_3529_;
goto v___jp_3520_;
}
}
}
v___jp_3545_:
{
lean_object* v_snd_3547_; lean_object* v_fst_3548_; lean_object* v_mctx_3549_; uint8_t v___x_3550_; 
v_snd_3547_ = lean_ctor_get(v___y_3546_, 1);
lean_inc(v_snd_3547_);
v_fst_3548_ = lean_ctor_get(v___y_3546_, 0);
lean_inc(v_fst_3548_);
lean_dec_ref(v___y_3546_);
v_mctx_3549_ = lean_ctor_get(v_snd_3547_, 1);
lean_inc_ref(v_mctx_3549_);
lean_dec(v_snd_3547_);
v___x_3550_ = lean_unbox(v_fst_3548_);
lean_dec(v_fst_3548_);
v_fst_3529_ = v___x_3550_;
v_mctx_3530_ = v_mctx_3549_;
goto v___jp_3528_;
}
}
else
{
uint8_t v_nondep_3558_; 
v_nondep_3558_ = lean_ctor_get_uint8(v_val_3519_, sizeof(void*)*5);
if (v_nondep_3558_ == 0)
{
lean_object* v_type_3559_; lean_object* v_value_3560_; lean_object* v___x_3561_; uint8_t v_fst_3563_; lean_object* v_snd_3564_; lean_object* v___y_3581_; lean_object* v_snd_3586_; lean_object* v___y_3592_; lean_object* v_mctx_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_type_3559_ = lean_ctor_get(v_val_3519_, 3);
v_value_3560_ = lean_ctor_get(v_val_3519_, 4);
v___x_3561_ = lean_st_ref_get(v___y_3499_);
v_mctx_3598_ = lean_ctor_get(v___x_3561_, 0);
lean_inc_ref(v_mctx_3598_);
lean_dec(v___x_3561_);
v___x_3599_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v_mctx_3598_);
v___x_3601_ = l_Lean_Expr_hasFVar(v_type_3559_);
if (v___x_3601_ == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = l_Lean_Expr_hasMVar(v_type_3559_);
if (v___x_3602_ == 0)
{
v_snd_3586_ = v___x_3600_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3603_; 
lean_inc_ref(v_type_3559_);
lean_inc_ref(v___f_3525_);
v___x_3603_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3559_, v___x_3600_);
v___y_3592_ = v___x_3603_;
goto v___jp_3591_;
}
}
else
{
lean_object* v___x_3604_; 
lean_inc_ref(v_type_3559_);
lean_inc_ref(v___f_3525_);
v___x_3604_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3559_, v___x_3600_);
v___y_3592_ = v___x_3604_;
goto v___jp_3591_;
}
v___jp_3562_:
{
lean_object* v_mctx_3565_; lean_object* v___x_3566_; lean_object* v_cache_3567_; lean_object* v_zetaDeltaFVarIds_3568_; lean_object* v_postponed_3569_; lean_object* v_diag_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3578_; 
v_mctx_3565_ = lean_ctor_get(v_snd_3564_, 1);
lean_inc_ref(v_mctx_3565_);
lean_dec_ref(v_snd_3564_);
v___x_3566_ = lean_st_ref_take(v___y_3499_);
v_cache_3567_ = lean_ctor_get(v___x_3566_, 1);
v_zetaDeltaFVarIds_3568_ = lean_ctor_get(v___x_3566_, 2);
v_postponed_3569_ = lean_ctor_get(v___x_3566_, 3);
v_diag_3570_ = lean_ctor_get(v___x_3566_, 4);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v___x_3566_, 0);
lean_dec(v_unused_3579_);
v___x_3572_ = v___x_3566_;
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_diag_3570_);
lean_inc(v_postponed_3569_);
lean_inc(v_zetaDeltaFVarIds_3568_);
lean_inc(v_cache_3567_);
lean_dec(v___x_3566_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_mctx_3565_);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_mctx_3565_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_cache_3567_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_zetaDeltaFVarIds_3568_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_postponed_3569_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_diag_3570_);
v___x_3575_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_st_ref_put(v___y_3499_, v___x_3575_);
v_a_3521_ = v_fst_3563_;
goto v___jp_3520_;
}
}
}
v___jp_3580_:
{
lean_object* v_fst_3582_; lean_object* v_snd_3583_; uint8_t v___x_3584_; 
v_fst_3582_ = lean_ctor_get(v___y_3581_, 0);
lean_inc(v_fst_3582_);
v_snd_3583_ = lean_ctor_get(v___y_3581_, 1);
lean_inc(v_snd_3583_);
lean_dec_ref(v___y_3581_);
v___x_3584_ = lean_unbox(v_fst_3582_);
lean_dec(v_fst_3582_);
v_fst_3563_ = v___x_3584_;
v_snd_3564_ = v_snd_3583_;
goto v___jp_3562_;
}
v___jp_3585_:
{
uint8_t v___x_3587_; 
v___x_3587_ = l_Lean_Expr_hasFVar(v_value_3560_);
if (v___x_3587_ == 0)
{
uint8_t v___x_3588_; 
v___x_3588_ = l_Lean_Expr_hasMVar(v_value_3560_);
if (v___x_3588_ == 0)
{
lean_dec_ref(v___f_3525_);
v_fst_3563_ = v___x_3588_;
v_snd_3564_ = v_snd_3586_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3589_; 
lean_inc_ref(v_value_3560_);
v___x_3589_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_value_3560_, v_snd_3586_);
v___y_3581_ = v___x_3589_;
goto v___jp_3580_;
}
}
else
{
lean_object* v___x_3590_; 
lean_inc_ref(v_value_3560_);
v___x_3590_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_value_3560_, v_snd_3586_);
v___y_3581_ = v___x_3590_;
goto v___jp_3580_;
}
}
v___jp_3591_:
{
lean_object* v_fst_3593_; uint8_t v___x_3594_; 
v_fst_3593_ = lean_ctor_get(v___y_3592_, 0);
v___x_3594_ = lean_unbox(v_fst_3593_);
if (v___x_3594_ == 0)
{
lean_object* v_snd_3595_; 
v_snd_3595_ = lean_ctor_get(v___y_3592_, 1);
lean_inc(v_snd_3595_);
lean_dec_ref(v___y_3592_);
v_snd_3586_ = v_snd_3595_;
goto v___jp_3585_;
}
else
{
lean_object* v_snd_3596_; uint8_t v___x_3597_; 
lean_inc(v_fst_3593_);
lean_dec_ref(v___f_3525_);
v_snd_3596_ = lean_ctor_get(v___y_3592_, 1);
lean_inc(v_snd_3596_);
lean_dec_ref(v___y_3592_);
v___x_3597_ = lean_unbox(v_fst_3593_);
lean_dec(v_fst_3593_);
v_fst_3563_ = v___x_3597_;
v_snd_3564_ = v_snd_3596_;
goto v___jp_3562_;
}
}
}
else
{
lean_object* v_type_3605_; lean_object* v___x_3606_; uint8_t v_fst_3608_; lean_object* v_mctx_3609_; lean_object* v___y_3625_; lean_object* v_mctx_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v_type_3605_ = lean_ctor_get(v_val_3519_, 3);
v___x_3606_ = lean_st_ref_get(v___y_3499_);
v_mctx_3630_ = lean_ctor_get(v___x_3606_, 0);
lean_inc_ref_n(v_mctx_3630_, 2);
lean_dec(v___x_3606_);
v___x_3631_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
lean_ctor_set(v___x_3632_, 1, v_mctx_3630_);
v___x_3633_ = l_Lean_Expr_hasFVar(v_type_3605_);
if (v___x_3633_ == 0)
{
uint8_t v___x_3634_; 
v___x_3634_ = l_Lean_Expr_hasMVar(v_type_3605_);
if (v___x_3634_ == 0)
{
lean_dec_ref_known(v___x_3632_, 2);
lean_dec_ref(v___f_3525_);
v_fst_3608_ = v___x_3634_;
v_mctx_3609_ = v_mctx_3630_;
goto v___jp_3607_;
}
else
{
lean_object* v___x_3635_; 
lean_dec_ref(v_mctx_3630_);
lean_inc_ref(v_type_3605_);
v___x_3635_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3605_, v___x_3632_);
v___y_3625_ = v___x_3635_;
goto v___jp_3624_;
}
}
else
{
lean_object* v___x_3636_; 
lean_dec_ref(v_mctx_3630_);
lean_inc_ref(v_type_3605_);
v___x_3636_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3525_, v___f_3524_, v_type_3605_, v___x_3632_);
v___y_3625_ = v___x_3636_;
goto v___jp_3624_;
}
v___jp_3607_:
{
lean_object* v___x_3610_; lean_object* v_cache_3611_; lean_object* v_zetaDeltaFVarIds_3612_; lean_object* v_postponed_3613_; lean_object* v_diag_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v___x_3610_ = lean_st_ref_take(v___y_3499_);
v_cache_3611_ = lean_ctor_get(v___x_3610_, 1);
v_zetaDeltaFVarIds_3612_ = lean_ctor_get(v___x_3610_, 2);
v_postponed_3613_ = lean_ctor_get(v___x_3610_, 3);
v_diag_3614_ = lean_ctor_get(v___x_3610_, 4);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3610_, 0);
lean_dec(v_unused_3623_);
v___x_3616_ = v___x_3610_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_diag_3614_);
lean_inc(v_postponed_3613_);
lean_inc(v_zetaDeltaFVarIds_3612_);
lean_inc(v_cache_3611_);
lean_dec(v___x_3610_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v_mctx_3609_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_mctx_3609_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_cache_3611_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_zetaDeltaFVarIds_3612_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_postponed_3613_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_diag_3614_);
v___x_3619_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_st_ref_put(v___y_3499_, v___x_3619_);
v_a_3521_ = v_fst_3608_;
goto v___jp_3520_;
}
}
}
v___jp_3624_:
{
lean_object* v_snd_3626_; lean_object* v_fst_3627_; lean_object* v_mctx_3628_; uint8_t v___x_3629_; 
v_snd_3626_ = lean_ctor_get(v___y_3625_, 1);
lean_inc(v_snd_3626_);
v_fst_3627_ = lean_ctor_get(v___y_3625_, 0);
lean_inc(v_fst_3627_);
lean_dec_ref(v___y_3625_);
v_mctx_3628_ = lean_ctor_get(v_snd_3626_, 1);
lean_inc_ref(v_mctx_3628_);
lean_dec(v_snd_3626_);
v___x_3629_ = lean_unbox(v_fst_3627_);
lean_dec(v_fst_3627_);
v_fst_3608_ = v___x_3629_;
v_mctx_3609_ = v_mctx_3628_;
goto v___jp_3607_;
}
}
}
v___jp_3520_:
{
if (v_a_3521_ == 0)
{
v_a_3511_ = v_snd_3505_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = l_Lean_LocalDecl_fvarId(v_val_3519_);
v___x_3523_ = lean_array_push(v_snd_3505_, v___x_3522_);
v_a_3511_ = v___x_3523_;
goto v___jp_3510_;
}
}
}
v___jp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v_a_3511_);
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3513_ = v___x_3507_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_a_3511_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3496_, v___x_3514_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3494_, v_sz_3495_, v___x_3515_, v___x_3513_, v___y_3499_);
return v___x_3516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3639_, lean_object* v_sz_3640_, lean_object* v_i_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
size_t v_sz_boxed_3648_; size_t v_i_boxed_3649_; lean_object* v_res_3650_; 
v_sz_boxed_3648_ = lean_unbox_usize(v_sz_3640_);
lean_dec(v_sz_3640_);
v_i_boxed_3649_ = lean_unbox_usize(v_i_3641_);
lean_dec(v_i_3641_);
v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3639_, v_sz_boxed_3648_, v_i_boxed_3649_, v_b_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v_as_3639_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3651_, lean_object* v_n_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
if (lean_obj_tag(v_n_3652_) == 0)
{
lean_object* v_cs_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; size_t v_sz_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v_cs_3659_ = lean_ctor_get(v_n_3652_, 0);
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v_b_3653_);
v_sz_3662_ = lean_array_size(v_cs_3659_);
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3651_, v_cs_3659_, v_sz_3662_, v___x_3663_, v___x_3661_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3679_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3679_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3679_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_fst_3669_; 
v_fst_3669_ = lean_ctor_get(v_a_3665_, 0);
if (lean_obj_tag(v_fst_3669_) == 0)
{
lean_object* v_snd_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v_snd_3670_ = lean_ctor_get(v_a_3665_, 1);
lean_inc(v_snd_3670_);
lean_dec(v_a_3665_);
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_snd_3670_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3671_);
v___x_3673_ = v___x_3667_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
else
{
lean_object* v_val_3675_; lean_object* v___x_3677_; 
lean_inc_ref(v_fst_3669_);
lean_dec(v_a_3665_);
v_val_3675_ = lean_ctor_get(v_fst_3669_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v_fst_3669_, 1);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v_val_3675_);
v___x_3677_ = v___x_3667_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_val_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3664_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3664_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_vs_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; size_t v_sz_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v_vs_3688_ = lean_ctor_get(v_n_3652_, 0);
v___x_3689_ = lean_box(0);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_b_3653_);
v_sz_3691_ = lean_array_size(v_vs_3688_);
v___x_3692_ = ((size_t)0ULL);
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3688_, v_sz_3691_, v___x_3692_, v___x_3690_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3708_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3708_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3708_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v_fst_3698_; 
v_fst_3698_ = lean_ctor_get(v_a_3694_, 0);
if (lean_obj_tag(v_fst_3698_) == 0)
{
lean_object* v_snd_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v_snd_3699_ = lean_ctor_get(v_a_3694_, 1);
lean_inc(v_snd_3699_);
lean_dec(v_a_3694_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_snd_3699_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3700_);
v___x_3702_ = v___x_3696_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
else
{
lean_object* v_val_3704_; lean_object* v___x_3706_; 
lean_inc_ref(v_fst_3698_);
lean_dec(v_a_3694_);
v_val_3704_ = lean_ctor_get(v_fst_3698_, 0);
lean_inc(v_val_3704_);
lean_dec_ref_known(v_fst_3698_, 1);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v_val_3704_);
v___x_3706_ = v___x_3696_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_val_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
v_a_3709_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3693_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3693_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3717_, lean_object* v_as_3718_, size_t v_sz_3719_, size_t v_i_3720_, lean_object* v_b_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = lean_usize_dec_lt(v_i_3720_, v_sz_3719_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v_b_3721_);
return v___x_3728_;
}
else
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3763_; 
v_snd_3729_ = lean_ctor_get(v_b_3721_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_b_3721_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v_b_3721_, 0);
lean_dec(v_unused_3764_);
v___x_3731_ = v_b_3721_;
v_isShared_3732_ = v_isSharedCheck_3763_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_snd_3729_);
lean_dec(v_b_3721_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3763_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; lean_object* v_a_3734_; lean_object* v___x_3735_; 
v___x_3733_ = lean_box(0);
v_a_3734_ = lean_array_uget_borrowed(v_as_3718_, v_i_3720_);
lean_inc(v_snd_3729_);
v___x_3735_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3717_, v_a_3734_, v_snd_3729_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3754_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3738_ = v___x_3735_;
v_isShared_3739_ = v_isSharedCheck_3754_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3754_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
if (lean_obj_tag(v_a_3736_) == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v_a_3736_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v___x_3740_);
v___x_3742_ = v___x_3731_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_snd_3729_);
v___x_3742_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3744_; 
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3742_);
v___x_3744_ = v___x_3738_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; 
lean_del_object(v___x_3738_);
lean_dec(v_snd_3729_);
v_a_3747_ = lean_ctor_get(v_a_3736_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v_a_3736_, 1);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v_a_3747_);
lean_ctor_set(v___x_3731_, 0, v___x_3733_);
v___x_3749_ = v___x_3731_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_a_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
size_t v___x_3750_; size_t v___x_3751_; 
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_i_3720_, v___x_3750_);
v_i_3720_ = v___x_3751_;
v_b_3721_ = v___x_3749_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3731_);
lean_dec(v_snd_3729_);
v_a_3755_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3735_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3735_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3765_, lean_object* v_as_3766_, lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3765_, v_as_3766_, v_sz_boxed_3775_, v_i_boxed_3776_, v_b_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_as_3766_);
lean_dec_ref(v_init_3765_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3778_, lean_object* v_n_3779_, lean_object* v_b_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3778_, v_n_3779_, v_b_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_n_3779_);
lean_dec_ref(v_init_3778_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3787_, size_t v_sz_3788_, size_t v_i_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_b_3790_);
return v___x_3794_;
}
else
{
lean_object* v_snd_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3927_; 
v_snd_3795_ = lean_ctor_get(v_b_3790_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_b_3790_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_b_3790_, 0);
lean_dec(v_unused_3928_);
v___x_3797_ = v_b_3790_;
v_isShared_3798_ = v_isSharedCheck_3927_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_snd_3795_);
lean_dec(v_b_3790_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3927_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3799_; lean_object* v_a_3801_; lean_object* v_a_3808_; 
v___x_3799_ = lean_box(0);
v_a_3808_ = lean_array_uget_borrowed(v_as_3787_, v_i_3789_);
if (lean_obj_tag(v_a_3808_) == 0)
{
v_a_3801_ = v_snd_3795_;
goto v___jp_3800_;
}
else
{
lean_object* v_val_3809_; uint8_t v_a_3811_; lean_object* v___f_3814_; lean_object* v___f_3815_; 
v_val_3809_ = lean_ctor_get(v_a_3808_, 0);
v___f_3814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3795_);
v___f_3815_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3815_, 0, v_snd_3795_);
if (lean_obj_tag(v_val_3809_) == 0)
{
lean_object* v_type_3816_; lean_object* v___x_3817_; uint8_t v_fst_3819_; lean_object* v_mctx_3820_; lean_object* v___y_3836_; lean_object* v_mctx_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_type_3816_ = lean_ctor_get(v_val_3809_, 3);
v___x_3817_ = lean_st_ref_get(v___y_3791_);
v_mctx_3841_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_ref_n(v_mctx_3841_, 2);
lean_dec(v___x_3817_);
v___x_3842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v_mctx_3841_);
v___x_3844_ = l_Lean_Expr_hasFVar(v_type_3816_);
if (v___x_3844_ == 0)
{
uint8_t v___x_3845_; 
v___x_3845_ = l_Lean_Expr_hasMVar(v_type_3816_);
if (v___x_3845_ == 0)
{
lean_dec_ref_known(v___x_3843_, 2);
lean_dec_ref(v___f_3815_);
v_fst_3819_ = v___x_3845_;
v_mctx_3820_ = v_mctx_3841_;
goto v___jp_3818_;
}
else
{
lean_object* v___x_3846_; 
lean_dec_ref(v_mctx_3841_);
lean_inc_ref(v_type_3816_);
v___x_3846_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3816_, v___x_3843_);
v___y_3836_ = v___x_3846_;
goto v___jp_3835_;
}
}
else
{
lean_object* v___x_3847_; 
lean_dec_ref(v_mctx_3841_);
lean_inc_ref(v_type_3816_);
v___x_3847_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3816_, v___x_3843_);
v___y_3836_ = v___x_3847_;
goto v___jp_3835_;
}
v___jp_3818_:
{
lean_object* v___x_3821_; lean_object* v_cache_3822_; lean_object* v_zetaDeltaFVarIds_3823_; lean_object* v_postponed_3824_; lean_object* v_diag_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
v___x_3821_ = lean_st_ref_take(v___y_3791_);
v_cache_3822_ = lean_ctor_get(v___x_3821_, 1);
v_zetaDeltaFVarIds_3823_ = lean_ctor_get(v___x_3821_, 2);
v_postponed_3824_ = lean_ctor_get(v___x_3821_, 3);
v_diag_3825_ = lean_ctor_get(v___x_3821_, 4);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v___x_3821_, 0);
lean_dec(v_unused_3834_);
v___x_3827_ = v___x_3821_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_diag_3825_);
lean_inc(v_postponed_3824_);
lean_inc(v_zetaDeltaFVarIds_3823_);
lean_inc(v_cache_3822_);
lean_dec(v___x_3821_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v_mctx_3820_);
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_mctx_3820_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_cache_3822_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_zetaDeltaFVarIds_3823_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_postponed_3824_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_diag_3825_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_st_ref_put(v___y_3791_, v___x_3830_);
v_a_3811_ = v_fst_3819_;
goto v___jp_3810_;
}
}
}
v___jp_3835_:
{
lean_object* v_snd_3837_; lean_object* v_fst_3838_; lean_object* v_mctx_3839_; uint8_t v___x_3840_; 
v_snd_3837_ = lean_ctor_get(v___y_3836_, 1);
lean_inc(v_snd_3837_);
v_fst_3838_ = lean_ctor_get(v___y_3836_, 0);
lean_inc(v_fst_3838_);
lean_dec_ref(v___y_3836_);
v_mctx_3839_ = lean_ctor_get(v_snd_3837_, 1);
lean_inc_ref(v_mctx_3839_);
lean_dec(v_snd_3837_);
v___x_3840_ = lean_unbox(v_fst_3838_);
lean_dec(v_fst_3838_);
v_fst_3819_ = v___x_3840_;
v_mctx_3820_ = v_mctx_3839_;
goto v___jp_3818_;
}
}
else
{
uint8_t v_nondep_3848_; 
v_nondep_3848_ = lean_ctor_get_uint8(v_val_3809_, sizeof(void*)*5);
if (v_nondep_3848_ == 0)
{
lean_object* v_type_3849_; lean_object* v_value_3850_; lean_object* v___x_3851_; uint8_t v_fst_3853_; lean_object* v_snd_3854_; lean_object* v___y_3871_; lean_object* v_snd_3876_; lean_object* v___y_3882_; lean_object* v_mctx_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v_type_3849_ = lean_ctor_get(v_val_3809_, 3);
v_value_3850_ = lean_ctor_get(v_val_3809_, 4);
v___x_3851_ = lean_st_ref_get(v___y_3791_);
v_mctx_3888_ = lean_ctor_get(v___x_3851_, 0);
lean_inc_ref(v_mctx_3888_);
lean_dec(v___x_3851_);
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v_mctx_3888_);
v___x_3891_ = l_Lean_Expr_hasFVar(v_type_3849_);
if (v___x_3891_ == 0)
{
uint8_t v___x_3892_; 
v___x_3892_ = l_Lean_Expr_hasMVar(v_type_3849_);
if (v___x_3892_ == 0)
{
v_snd_3876_ = v___x_3890_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3893_; 
lean_inc_ref(v_type_3849_);
lean_inc_ref(v___f_3815_);
v___x_3893_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3849_, v___x_3890_);
v___y_3882_ = v___x_3893_;
goto v___jp_3881_;
}
}
else
{
lean_object* v___x_3894_; 
lean_inc_ref(v_type_3849_);
lean_inc_ref(v___f_3815_);
v___x_3894_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3849_, v___x_3890_);
v___y_3882_ = v___x_3894_;
goto v___jp_3881_;
}
v___jp_3852_:
{
lean_object* v_mctx_3855_; lean_object* v___x_3856_; lean_object* v_cache_3857_; lean_object* v_zetaDeltaFVarIds_3858_; lean_object* v_postponed_3859_; lean_object* v_diag_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3868_; 
v_mctx_3855_ = lean_ctor_get(v_snd_3854_, 1);
lean_inc_ref(v_mctx_3855_);
lean_dec_ref(v_snd_3854_);
v___x_3856_ = lean_st_ref_take(v___y_3791_);
v_cache_3857_ = lean_ctor_get(v___x_3856_, 1);
v_zetaDeltaFVarIds_3858_ = lean_ctor_get(v___x_3856_, 2);
v_postponed_3859_ = lean_ctor_get(v___x_3856_, 3);
v_diag_3860_ = lean_ctor_get(v___x_3856_, 4);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v___x_3856_, 0);
lean_dec(v_unused_3869_);
v___x_3862_ = v___x_3856_;
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_diag_3860_);
lean_inc(v_postponed_3859_);
lean_inc(v_zetaDeltaFVarIds_3858_);
lean_inc(v_cache_3857_);
lean_dec(v___x_3856_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v_mctx_3855_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_mctx_3855_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_cache_3857_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_zetaDeltaFVarIds_3858_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_postponed_3859_);
lean_ctor_set(v_reuseFailAlloc_3867_, 4, v_diag_3860_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_st_ref_put(v___y_3791_, v___x_3865_);
v_a_3811_ = v_fst_3853_;
goto v___jp_3810_;
}
}
}
v___jp_3870_:
{
lean_object* v_fst_3872_; lean_object* v_snd_3873_; uint8_t v___x_3874_; 
v_fst_3872_ = lean_ctor_get(v___y_3871_, 0);
lean_inc(v_fst_3872_);
v_snd_3873_ = lean_ctor_get(v___y_3871_, 1);
lean_inc(v_snd_3873_);
lean_dec_ref(v___y_3871_);
v___x_3874_ = lean_unbox(v_fst_3872_);
lean_dec(v_fst_3872_);
v_fst_3853_ = v___x_3874_;
v_snd_3854_ = v_snd_3873_;
goto v___jp_3852_;
}
v___jp_3875_:
{
uint8_t v___x_3877_; 
v___x_3877_ = l_Lean_Expr_hasFVar(v_value_3850_);
if (v___x_3877_ == 0)
{
uint8_t v___x_3878_; 
v___x_3878_ = l_Lean_Expr_hasMVar(v_value_3850_);
if (v___x_3878_ == 0)
{
lean_dec_ref(v___f_3815_);
v_fst_3853_ = v___x_3878_;
v_snd_3854_ = v_snd_3876_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3879_; 
lean_inc_ref(v_value_3850_);
v___x_3879_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_value_3850_, v_snd_3876_);
v___y_3871_ = v___x_3879_;
goto v___jp_3870_;
}
}
else
{
lean_object* v___x_3880_; 
lean_inc_ref(v_value_3850_);
v___x_3880_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_value_3850_, v_snd_3876_);
v___y_3871_ = v___x_3880_;
goto v___jp_3870_;
}
}
v___jp_3881_:
{
lean_object* v_fst_3883_; uint8_t v___x_3884_; 
v_fst_3883_ = lean_ctor_get(v___y_3882_, 0);
v___x_3884_ = lean_unbox(v_fst_3883_);
if (v___x_3884_ == 0)
{
lean_object* v_snd_3885_; 
v_snd_3885_ = lean_ctor_get(v___y_3882_, 1);
lean_inc(v_snd_3885_);
lean_dec_ref(v___y_3882_);
v_snd_3876_ = v_snd_3885_;
goto v___jp_3875_;
}
else
{
lean_object* v_snd_3886_; uint8_t v___x_3887_; 
lean_inc(v_fst_3883_);
lean_dec_ref(v___f_3815_);
v_snd_3886_ = lean_ctor_get(v___y_3882_, 1);
lean_inc(v_snd_3886_);
lean_dec_ref(v___y_3882_);
v___x_3887_ = lean_unbox(v_fst_3883_);
lean_dec(v_fst_3883_);
v_fst_3853_ = v___x_3887_;
v_snd_3854_ = v_snd_3886_;
goto v___jp_3852_;
}
}
}
else
{
lean_object* v_type_3895_; lean_object* v___x_3896_; uint8_t v_fst_3898_; lean_object* v_mctx_3899_; lean_object* v___y_3915_; lean_object* v_mctx_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_type_3895_ = lean_ctor_get(v_val_3809_, 3);
v___x_3896_ = lean_st_ref_get(v___y_3791_);
v_mctx_3920_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_ref_n(v_mctx_3920_, 2);
lean_dec(v___x_3896_);
v___x_3921_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v_mctx_3920_);
v___x_3923_ = l_Lean_Expr_hasFVar(v_type_3895_);
if (v___x_3923_ == 0)
{
uint8_t v___x_3924_; 
v___x_3924_ = l_Lean_Expr_hasMVar(v_type_3895_);
if (v___x_3924_ == 0)
{
lean_dec_ref_known(v___x_3922_, 2);
lean_dec_ref(v___f_3815_);
v_fst_3898_ = v___x_3924_;
v_mctx_3899_ = v_mctx_3920_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3925_; 
lean_dec_ref(v_mctx_3920_);
lean_inc_ref(v_type_3895_);
v___x_3925_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3895_, v___x_3922_);
v___y_3915_ = v___x_3925_;
goto v___jp_3914_;
}
}
else
{
lean_object* v___x_3926_; 
lean_dec_ref(v_mctx_3920_);
lean_inc_ref(v_type_3895_);
v___x_3926_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3815_, v___f_3814_, v_type_3895_, v___x_3922_);
v___y_3915_ = v___x_3926_;
goto v___jp_3914_;
}
v___jp_3897_:
{
lean_object* v___x_3900_; lean_object* v_cache_3901_; lean_object* v_zetaDeltaFVarIds_3902_; lean_object* v_postponed_3903_; lean_object* v_diag_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3912_; 
v___x_3900_ = lean_st_ref_take(v___y_3791_);
v_cache_3901_ = lean_ctor_get(v___x_3900_, 1);
v_zetaDeltaFVarIds_3902_ = lean_ctor_get(v___x_3900_, 2);
v_postponed_3903_ = lean_ctor_get(v___x_3900_, 3);
v_diag_3904_ = lean_ctor_get(v___x_3900_, 4);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; 
v_unused_3913_ = lean_ctor_get(v___x_3900_, 0);
lean_dec(v_unused_3913_);
v___x_3906_ = v___x_3900_;
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_diag_3904_);
lean_inc(v_postponed_3903_);
lean_inc(v_zetaDeltaFVarIds_3902_);
lean_inc(v_cache_3901_);
lean_dec(v___x_3900_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_mctx_3899_);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_mctx_3899_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_cache_3901_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_zetaDeltaFVarIds_3902_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_postponed_3903_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_diag_3904_);
v___x_3909_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_st_ref_put(v___y_3791_, v___x_3909_);
v_a_3811_ = v_fst_3898_;
goto v___jp_3810_;
}
}
}
v___jp_3914_:
{
lean_object* v_snd_3916_; lean_object* v_fst_3917_; lean_object* v_mctx_3918_; uint8_t v___x_3919_; 
v_snd_3916_ = lean_ctor_get(v___y_3915_, 1);
lean_inc(v_snd_3916_);
v_fst_3917_ = lean_ctor_get(v___y_3915_, 0);
lean_inc(v_fst_3917_);
lean_dec_ref(v___y_3915_);
v_mctx_3918_ = lean_ctor_get(v_snd_3916_, 1);
lean_inc_ref(v_mctx_3918_);
lean_dec(v_snd_3916_);
v___x_3919_ = lean_unbox(v_fst_3917_);
lean_dec(v_fst_3917_);
v_fst_3898_ = v___x_3919_;
v_mctx_3899_ = v_mctx_3918_;
goto v___jp_3897_;
}
}
}
v___jp_3810_:
{
if (v_a_3811_ == 0)
{
v_a_3801_ = v_snd_3795_;
goto v___jp_3800_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = l_Lean_LocalDecl_fvarId(v_val_3809_);
v___x_3813_ = lean_array_push(v_snd_3795_, v___x_3812_);
v_a_3801_ = v___x_3813_;
goto v___jp_3800_;
}
}
}
v___jp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v_a_3801_);
lean_ctor_set(v___x_3797_, 0, v___x_3799_);
v___x_3803_ = v___x_3797_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_a_3801_);
v___x_3803_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
size_t v___x_3804_; size_t v___x_3805_; 
v___x_3804_ = ((size_t)1ULL);
v___x_3805_ = lean_usize_add(v_i_3789_, v___x_3804_);
v_i_3789_ = v___x_3805_;
v_b_3790_ = v___x_3803_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3929_, lean_object* v_sz_3930_, lean_object* v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
size_t v_sz_boxed_3935_; size_t v_i_boxed_3936_; lean_object* v_res_3937_; 
v_sz_boxed_3935_ = lean_unbox_usize(v_sz_3930_);
lean_dec(v_sz_3930_);
v_i_boxed_3936_ = lean_unbox_usize(v_i_3931_);
lean_dec(v_i_3931_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3929_, v_sz_boxed_3935_, v_i_boxed_3936_, v_b_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v_as_3929_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3938_, size_t v_sz_3939_, size_t v_i_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_usize_dec_lt(v_i_3940_, v_sz_3939_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_b_3941_);
return v___x_3948_;
}
else
{
lean_object* v_snd_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_4081_; 
v_snd_3949_ = lean_ctor_get(v_b_3941_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_b_3941_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v_b_3941_, 0);
lean_dec(v_unused_4082_);
v___x_3951_ = v_b_3941_;
v_isShared_3952_ = v_isSharedCheck_4081_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_snd_3949_);
lean_dec(v_b_3941_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_4081_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v_a_3955_; lean_object* v_a_3962_; 
v___x_3953_ = lean_box(0);
v_a_3962_ = lean_array_uget_borrowed(v_as_3938_, v_i_3940_);
if (lean_obj_tag(v_a_3962_) == 0)
{
v_a_3955_ = v_snd_3949_;
goto v___jp_3954_;
}
else
{
lean_object* v_val_3963_; uint8_t v_a_3965_; lean_object* v___f_3968_; lean_object* v___f_3969_; 
v_val_3963_ = lean_ctor_get(v_a_3962_, 0);
v___f_3968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3949_);
v___f_3969_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3969_, 0, v_snd_3949_);
if (lean_obj_tag(v_val_3963_) == 0)
{
lean_object* v_type_3970_; lean_object* v___x_3971_; uint8_t v_fst_3973_; lean_object* v_mctx_3974_; lean_object* v___y_3990_; lean_object* v_mctx_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v_type_3970_ = lean_ctor_get(v_val_3963_, 3);
v___x_3971_ = lean_st_ref_get(v___y_3943_);
v_mctx_3995_ = lean_ctor_get(v___x_3971_, 0);
lean_inc_ref_n(v_mctx_3995_, 2);
lean_dec(v___x_3971_);
v___x_3996_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v_mctx_3995_);
v___x_3998_ = l_Lean_Expr_hasFVar(v_type_3970_);
if (v___x_3998_ == 0)
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Lean_Expr_hasMVar(v_type_3970_);
if (v___x_3999_ == 0)
{
lean_dec_ref_known(v___x_3997_, 2);
lean_dec_ref(v___f_3969_);
v_fst_3973_ = v___x_3999_;
v_mctx_3974_ = v_mctx_3995_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_4000_; 
lean_dec_ref(v_mctx_3995_);
lean_inc_ref(v_type_3970_);
v___x_4000_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_3970_, v___x_3997_);
v___y_3990_ = v___x_4000_;
goto v___jp_3989_;
}
}
else
{
lean_object* v___x_4001_; 
lean_dec_ref(v_mctx_3995_);
lean_inc_ref(v_type_3970_);
v___x_4001_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_3970_, v___x_3997_);
v___y_3990_ = v___x_4001_;
goto v___jp_3989_;
}
v___jp_3972_:
{
lean_object* v___x_3975_; lean_object* v_cache_3976_; lean_object* v_zetaDeltaFVarIds_3977_; lean_object* v_postponed_3978_; lean_object* v_diag_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3987_; 
v___x_3975_ = lean_st_ref_take(v___y_3943_);
v_cache_3976_ = lean_ctor_get(v___x_3975_, 1);
v_zetaDeltaFVarIds_3977_ = lean_ctor_get(v___x_3975_, 2);
v_postponed_3978_ = lean_ctor_get(v___x_3975_, 3);
v_diag_3979_ = lean_ctor_get(v___x_3975_, 4);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v___x_3975_, 0);
lean_dec(v_unused_3988_);
v___x_3981_ = v___x_3975_;
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_diag_3979_);
lean_inc(v_postponed_3978_);
lean_inc(v_zetaDeltaFVarIds_3977_);
lean_inc(v_cache_3976_);
lean_dec(v___x_3975_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v_mctx_3974_);
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_mctx_3974_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_cache_3976_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_zetaDeltaFVarIds_3977_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_postponed_3978_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v_diag_3979_);
v___x_3984_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_st_ref_put(v___y_3943_, v___x_3984_);
v_a_3965_ = v_fst_3973_;
goto v___jp_3964_;
}
}
}
v___jp_3989_:
{
lean_object* v_snd_3991_; lean_object* v_fst_3992_; lean_object* v_mctx_3993_; uint8_t v___x_3994_; 
v_snd_3991_ = lean_ctor_get(v___y_3990_, 1);
lean_inc(v_snd_3991_);
v_fst_3992_ = lean_ctor_get(v___y_3990_, 0);
lean_inc(v_fst_3992_);
lean_dec_ref(v___y_3990_);
v_mctx_3993_ = lean_ctor_get(v_snd_3991_, 1);
lean_inc_ref(v_mctx_3993_);
lean_dec(v_snd_3991_);
v___x_3994_ = lean_unbox(v_fst_3992_);
lean_dec(v_fst_3992_);
v_fst_3973_ = v___x_3994_;
v_mctx_3974_ = v_mctx_3993_;
goto v___jp_3972_;
}
}
else
{
uint8_t v_nondep_4002_; 
v_nondep_4002_ = lean_ctor_get_uint8(v_val_3963_, sizeof(void*)*5);
if (v_nondep_4002_ == 0)
{
lean_object* v_type_4003_; lean_object* v_value_4004_; lean_object* v___x_4005_; uint8_t v_fst_4007_; lean_object* v_snd_4008_; lean_object* v___y_4025_; lean_object* v_snd_4030_; lean_object* v___y_4036_; lean_object* v_mctx_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v_type_4003_ = lean_ctor_get(v_val_3963_, 3);
v_value_4004_ = lean_ctor_get(v_val_3963_, 4);
v___x_4005_ = lean_st_ref_get(v___y_3943_);
v_mctx_4042_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_ref(v_mctx_4042_);
lean_dec(v___x_4005_);
v___x_4043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v_mctx_4042_);
v___x_4045_ = l_Lean_Expr_hasFVar(v_type_4003_);
if (v___x_4045_ == 0)
{
uint8_t v___x_4046_; 
v___x_4046_ = l_Lean_Expr_hasMVar(v_type_4003_);
if (v___x_4046_ == 0)
{
v_snd_4030_ = v___x_4044_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4047_; 
lean_inc_ref(v_type_4003_);
lean_inc_ref(v___f_3969_);
v___x_4047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_4003_, v___x_4044_);
v___y_4036_ = v___x_4047_;
goto v___jp_4035_;
}
}
else
{
lean_object* v___x_4048_; 
lean_inc_ref(v_type_4003_);
lean_inc_ref(v___f_3969_);
v___x_4048_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_4003_, v___x_4044_);
v___y_4036_ = v___x_4048_;
goto v___jp_4035_;
}
v___jp_4006_:
{
lean_object* v_mctx_4009_; lean_object* v___x_4010_; lean_object* v_cache_4011_; lean_object* v_zetaDeltaFVarIds_4012_; lean_object* v_postponed_4013_; lean_object* v_diag_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4022_; 
v_mctx_4009_ = lean_ctor_get(v_snd_4008_, 1);
lean_inc_ref(v_mctx_4009_);
lean_dec_ref(v_snd_4008_);
v___x_4010_ = lean_st_ref_take(v___y_3943_);
v_cache_4011_ = lean_ctor_get(v___x_4010_, 1);
v_zetaDeltaFVarIds_4012_ = lean_ctor_get(v___x_4010_, 2);
v_postponed_4013_ = lean_ctor_get(v___x_4010_, 3);
v_diag_4014_ = lean_ctor_get(v___x_4010_, 4);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; 
v_unused_4023_ = lean_ctor_get(v___x_4010_, 0);
lean_dec(v_unused_4023_);
v___x_4016_ = v___x_4010_;
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_diag_4014_);
lean_inc(v_postponed_4013_);
lean_inc(v_zetaDeltaFVarIds_4012_);
lean_inc(v_cache_4011_);
lean_dec(v___x_4010_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v_mctx_4009_);
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_mctx_4009_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_cache_4011_);
lean_ctor_set(v_reuseFailAlloc_4021_, 2, v_zetaDeltaFVarIds_4012_);
lean_ctor_set(v_reuseFailAlloc_4021_, 3, v_postponed_4013_);
lean_ctor_set(v_reuseFailAlloc_4021_, 4, v_diag_4014_);
v___x_4019_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_st_ref_put(v___y_3943_, v___x_4019_);
v_a_3965_ = v_fst_4007_;
goto v___jp_3964_;
}
}
}
v___jp_4024_:
{
lean_object* v_fst_4026_; lean_object* v_snd_4027_; uint8_t v___x_4028_; 
v_fst_4026_ = lean_ctor_get(v___y_4025_, 0);
lean_inc(v_fst_4026_);
v_snd_4027_ = lean_ctor_get(v___y_4025_, 1);
lean_inc(v_snd_4027_);
lean_dec_ref(v___y_4025_);
v___x_4028_ = lean_unbox(v_fst_4026_);
lean_dec(v_fst_4026_);
v_fst_4007_ = v___x_4028_;
v_snd_4008_ = v_snd_4027_;
goto v___jp_4006_;
}
v___jp_4029_:
{
uint8_t v___x_4031_; 
v___x_4031_ = l_Lean_Expr_hasFVar(v_value_4004_);
if (v___x_4031_ == 0)
{
uint8_t v___x_4032_; 
v___x_4032_ = l_Lean_Expr_hasMVar(v_value_4004_);
if (v___x_4032_ == 0)
{
lean_dec_ref(v___f_3969_);
v_fst_4007_ = v___x_4032_;
v_snd_4008_ = v_snd_4030_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4033_; 
lean_inc_ref(v_value_4004_);
v___x_4033_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_value_4004_, v_snd_4030_);
v___y_4025_ = v___x_4033_;
goto v___jp_4024_;
}
}
else
{
lean_object* v___x_4034_; 
lean_inc_ref(v_value_4004_);
v___x_4034_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_value_4004_, v_snd_4030_);
v___y_4025_ = v___x_4034_;
goto v___jp_4024_;
}
}
v___jp_4035_:
{
lean_object* v_fst_4037_; uint8_t v___x_4038_; 
v_fst_4037_ = lean_ctor_get(v___y_4036_, 0);
v___x_4038_ = lean_unbox(v_fst_4037_);
if (v___x_4038_ == 0)
{
lean_object* v_snd_4039_; 
v_snd_4039_ = lean_ctor_get(v___y_4036_, 1);
lean_inc(v_snd_4039_);
lean_dec_ref(v___y_4036_);
v_snd_4030_ = v_snd_4039_;
goto v___jp_4029_;
}
else
{
lean_object* v_snd_4040_; uint8_t v___x_4041_; 
lean_inc(v_fst_4037_);
lean_dec_ref(v___f_3969_);
v_snd_4040_ = lean_ctor_get(v___y_4036_, 1);
lean_inc(v_snd_4040_);
lean_dec_ref(v___y_4036_);
v___x_4041_ = lean_unbox(v_fst_4037_);
lean_dec(v_fst_4037_);
v_fst_4007_ = v___x_4041_;
v_snd_4008_ = v_snd_4040_;
goto v___jp_4006_;
}
}
}
else
{
lean_object* v_type_4049_; lean_object* v___x_4050_; uint8_t v_fst_4052_; lean_object* v_mctx_4053_; lean_object* v___y_4069_; lean_object* v_mctx_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_type_4049_ = lean_ctor_get(v_val_3963_, 3);
v___x_4050_ = lean_st_ref_get(v___y_3943_);
v_mctx_4074_ = lean_ctor_get(v___x_4050_, 0);
lean_inc_ref_n(v_mctx_4074_, 2);
lean_dec(v___x_4050_);
v___x_4075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v_mctx_4074_);
v___x_4077_ = l_Lean_Expr_hasFVar(v_type_4049_);
if (v___x_4077_ == 0)
{
uint8_t v___x_4078_; 
v___x_4078_ = l_Lean_Expr_hasMVar(v_type_4049_);
if (v___x_4078_ == 0)
{
lean_dec_ref_known(v___x_4076_, 2);
lean_dec_ref(v___f_3969_);
v_fst_4052_ = v___x_4078_;
v_mctx_4053_ = v_mctx_4074_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4079_; 
lean_dec_ref(v_mctx_4074_);
lean_inc_ref(v_type_4049_);
v___x_4079_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_4049_, v___x_4076_);
v___y_4069_ = v___x_4079_;
goto v___jp_4068_;
}
}
else
{
lean_object* v___x_4080_; 
lean_dec_ref(v_mctx_4074_);
lean_inc_ref(v_type_4049_);
v___x_4080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3969_, v___f_3968_, v_type_4049_, v___x_4076_);
v___y_4069_ = v___x_4080_;
goto v___jp_4068_;
}
v___jp_4051_:
{
lean_object* v___x_4054_; lean_object* v_cache_4055_; lean_object* v_zetaDeltaFVarIds_4056_; lean_object* v_postponed_4057_; lean_object* v_diag_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4066_; 
v___x_4054_ = lean_st_ref_take(v___y_3943_);
v_cache_4055_ = lean_ctor_get(v___x_4054_, 1);
v_zetaDeltaFVarIds_4056_ = lean_ctor_get(v___x_4054_, 2);
v_postponed_4057_ = lean_ctor_get(v___x_4054_, 3);
v_diag_4058_ = lean_ctor_get(v___x_4054_, 4);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v___x_4054_, 0);
lean_dec(v_unused_4067_);
v___x_4060_ = v___x_4054_;
v_isShared_4061_ = v_isSharedCheck_4066_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_diag_4058_);
lean_inc(v_postponed_4057_);
lean_inc(v_zetaDeltaFVarIds_4056_);
lean_inc(v_cache_4055_);
lean_dec(v___x_4054_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4066_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v_mctx_4053_);
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_mctx_4053_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_cache_4055_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_zetaDeltaFVarIds_4056_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_postponed_4057_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v_diag_4058_);
v___x_4063_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_st_ref_put(v___y_3943_, v___x_4063_);
v_a_3965_ = v_fst_4052_;
goto v___jp_3964_;
}
}
}
v___jp_4068_:
{
lean_object* v_snd_4070_; lean_object* v_fst_4071_; lean_object* v_mctx_4072_; uint8_t v___x_4073_; 
v_snd_4070_ = lean_ctor_get(v___y_4069_, 1);
lean_inc(v_snd_4070_);
v_fst_4071_ = lean_ctor_get(v___y_4069_, 0);
lean_inc(v_fst_4071_);
lean_dec_ref(v___y_4069_);
v_mctx_4072_ = lean_ctor_get(v_snd_4070_, 1);
lean_inc_ref(v_mctx_4072_);
lean_dec(v_snd_4070_);
v___x_4073_ = lean_unbox(v_fst_4071_);
lean_dec(v_fst_4071_);
v_fst_4052_ = v___x_4073_;
v_mctx_4053_ = v_mctx_4072_;
goto v___jp_4051_;
}
}
}
v___jp_3964_:
{
if (v_a_3965_ == 0)
{
v_a_3955_ = v_snd_3949_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = l_Lean_LocalDecl_fvarId(v_val_3963_);
v___x_3967_ = lean_array_push(v_snd_3949_, v___x_3966_);
v_a_3955_ = v___x_3967_;
goto v___jp_3954_;
}
}
}
v___jp_3954_:
{
lean_object* v___x_3957_; 
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 1, v_a_3955_);
lean_ctor_set(v___x_3951_, 0, v___x_3953_);
v___x_3957_ = v___x_3951_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_a_3955_);
v___x_3957_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
size_t v___x_3958_; size_t v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = ((size_t)1ULL);
v___x_3959_ = lean_usize_add(v_i_3940_, v___x_3958_);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3938_, v_sz_3939_, v___x_3959_, v___x_3957_, v___y_3943_);
return v___x_3960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4083_, lean_object* v_sz_4084_, lean_object* v_i_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_sz_boxed_4092_; size_t v_i_boxed_4093_; lean_object* v_res_4094_; 
v_sz_boxed_4092_ = lean_unbox_usize(v_sz_4084_);
lean_dec(v_sz_4084_);
v_i_boxed_4093_ = lean_unbox_usize(v_i_4085_);
lean_dec(v_i_4085_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4083_, v_sz_boxed_4092_, v_i_boxed_4093_, v_b_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec_ref(v_as_4083_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4095_, lean_object* v_init_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_root_4102_; lean_object* v_tail_4103_; lean_object* v___x_4104_; 
v_root_4102_ = lean_ctor_get(v_t_4095_, 0);
v_tail_4103_ = lean_ctor_get(v_t_4095_, 1);
lean_inc_ref(v_init_4096_);
v___x_4104_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4096_, v_root_4102_, v_init_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec_ref(v_init_4096_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4141_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4107_ = v___x_4104_;
v_isShared_4108_ = v_isSharedCheck_4141_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4104_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4141_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
if (lean_obj_tag(v_a_4105_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; 
v_a_4109_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v_a_4105_, 1);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v_a_4109_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; size_t v_sz_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
lean_del_object(v___x_4107_);
v_a_4113_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v_a_4105_, 1);
v___x_4114_ = lean_box(0);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v_a_4113_);
v_sz_4116_ = lean_array_size(v_tail_4103_);
v___x_4117_ = ((size_t)0ULL);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4103_, v_sz_4116_, v___x_4117_, v___x_4115_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4132_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4132_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4132_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v_fst_4123_; 
v_fst_4123_ = lean_ctor_get(v_a_4119_, 0);
if (lean_obj_tag(v_fst_4123_) == 0)
{
lean_object* v_snd_4124_; lean_object* v___x_4126_; 
v_snd_4124_ = lean_ctor_get(v_a_4119_, 1);
lean_inc(v_snd_4124_);
lean_dec(v_a_4119_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v_snd_4124_);
v___x_4126_ = v___x_4121_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_snd_4124_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4130_; 
lean_inc_ref(v_fst_4123_);
lean_dec(v_a_4119_);
v_val_4128_ = lean_ctor_get(v_fst_4123_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v_fst_4123_, 1);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v_val_4128_);
v___x_4130_ = v___x_4121_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_val_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4118_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4118_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
v_a_4142_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4104_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4104_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4150_, lean_object* v_init_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4150_, v_init_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_t_4150_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4158_, lean_object* v_fvarIds_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___x_4165_; 
lean_inc(v_goal_4158_);
v___x_4165_ = l_Lean_MVarId_getDecl(v_goal_4158_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v_lctx_4167_; lean_object* v_decls_4168_; lean_object* v___x_4169_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v_lctx_4167_ = lean_ctor_get(v_a_4166_, 1);
lean_inc_ref(v_lctx_4167_);
lean_dec(v_a_4166_);
v_decls_4168_ = lean_ctor_get(v_lctx_4167_, 1);
lean_inc_ref(v_decls_4168_);
lean_dec_ref(v_lctx_4167_);
v___x_4169_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4168_, v_fvarIds_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec_ref(v_decls_4168_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4171_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4169_, 1);
v___x_4171_ = l_Lean_MVarId_tryClearMany(v_goal_4158_, v_a_4170_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4170_);
return v___x_4171_;
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_goal_4158_);
v_a_4172_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4169_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4169_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v_fvarIds_4159_);
lean_dec(v_goal_4158_);
v_a_4180_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4165_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4165_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4188_, lean_object* v_fvarIds_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4188_, v_fvarIds_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4196_, size_t v_sz_4197_, size_t v_i_4198_, lean_object* v_b_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4196_, v_sz_4197_, v_i_4198_, v_b_4199_, v___y_4201_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4206_, lean_object* v_sz_4207_, lean_object* v_i_4208_, lean_object* v_b_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
size_t v_sz_boxed_4215_; size_t v_i_boxed_4216_; lean_object* v_res_4217_; 
v_sz_boxed_4215_ = lean_unbox_usize(v_sz_4207_);
lean_dec(v_sz_4207_);
v_i_boxed_4216_ = lean_unbox_usize(v_i_4208_);
lean_dec(v_i_4208_);
v_res_4217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4206_, v_sz_boxed_4215_, v_i_boxed_4216_, v_b_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec_ref(v_as_4206_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4218_, size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4218_, v_sz_4219_, v_i_4220_, v_b_4221_, v___y_4223_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4228_, lean_object* v_sz_4229_, lean_object* v_i_4230_, lean_object* v_b_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
size_t v_sz_boxed_4237_; size_t v_i_boxed_4238_; lean_object* v_res_4239_; 
v_sz_boxed_4237_ = lean_unbox_usize(v_sz_4229_);
lean_dec(v_sz_4229_);
v_i_boxed_4238_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4228_, v_sz_boxed_4237_, v_i_boxed_4238_, v_b_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec_ref(v_as_4228_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4240_, lean_object* v_as_4241_, size_t v_sz_4242_, size_t v_i_4243_, lean_object* v_b_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
uint8_t v___x_4252_; 
v___x_4252_ = lean_usize_dec_lt(v_i_4243_, v_sz_4242_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v_b_4244_);
return v___x_4253_;
}
else
{
lean_object* v_a_4254_; lean_object* v_fst_4255_; lean_object* v_snd_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_a_4254_ = lean_array_uget_borrowed(v_as_4241_, v_i_4243_);
v_fst_4255_ = lean_ctor_get(v_a_4254_, 0);
v_snd_4256_ = lean_ctor_get(v_a_4254_, 1);
v___x_4257_ = lean_box(0);
lean_inc(v_snd_4256_);
v___x_4258_ = l_Lean_Meta_FVarSubst_get(v_fs_4240_, v_snd_4256_);
lean_inc(v_fst_4255_);
v___x_4259_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4255_, v___x_4258_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4259_) == 0)
{
size_t v___x_4260_; size_t v___x_4261_; 
lean_dec_ref_known(v___x_4259_, 1);
v___x_4260_ = ((size_t)1ULL);
v___x_4261_ = lean_usize_add(v_i_4243_, v___x_4260_);
v_i_4243_ = v___x_4261_;
v_b_4244_ = v___x_4257_;
goto _start;
}
else
{
return v___x_4259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4263_, lean_object* v_as_4264_, lean_object* v_sz_4265_, lean_object* v_i_4266_, lean_object* v_b_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
size_t v_sz_boxed_4275_; size_t v_i_boxed_4276_; lean_object* v_res_4277_; 
v_sz_boxed_4275_ = lean_unbox_usize(v_sz_4265_);
lean_dec(v_sz_4265_);
v_i_boxed_4276_ = lean_unbox_usize(v_i_4266_);
lean_dec(v_i_4266_);
v_res_4277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4263_, v_as_4264_, v_sz_boxed_4275_, v_i_boxed_4276_, v_b_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec_ref(v_as_4264_);
lean_dec(v_fs_4263_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4278_, lean_object* v_toTag_4279_, size_t v_sz_4280_, size_t v___x_4281_, lean_object* v___x_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4278_, v_toTag_4279_, v_sz_4280_, v___x_4281_, v___x_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4297_ == 0)
{
lean_object* v_unused_4298_; 
v_unused_4298_ = lean_ctor_get(v___x_4290_, 0);
lean_dec(v_unused_4298_);
v___x_4292_ = v___x_4290_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_dec(v___x_4290_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4282_);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4282_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
else
{
return v___x_4290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4299_, lean_object* v_toTag_4300_, lean_object* v_sz_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
size_t v_sz_boxed_4311_; size_t v___x_1634__boxed_4312_; lean_object* v_res_4313_; 
v_sz_boxed_4311_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v___x_1634__boxed_4312_ = lean_unbox_usize(v___x_4302_);
lean_dec(v___x_4302_);
v_res_4313_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4299_, v_toTag_4300_, v_sz_boxed_4311_, v___x_1634__boxed_4312_, v___x_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_toTag_4300_);
lean_dec(v_fs_4299_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4314_, size_t v_i_4315_, size_t v_stop_4316_, lean_object* v_b_4317_){
_start:
{
lean_object* v___y_4319_; uint8_t v___x_4323_; 
v___x_4323_ = lean_usize_dec_eq(v_i_4315_, v_stop_4316_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = lean_array_uget_borrowed(v_as_4314_, v_i_4315_);
v___x_4325_ = l_Lean_Expr_isFVar(v___x_4324_);
if (v___x_4325_ == 0)
{
v___y_4319_ = v_b_4317_;
goto v___jp_4318_;
}
else
{
lean_object* v___x_4326_; 
lean_inc(v___x_4324_);
v___x_4326_ = lean_array_push(v_b_4317_, v___x_4324_);
v___y_4319_ = v___x_4326_;
goto v___jp_4318_;
}
}
else
{
return v_b_4317_;
}
v___jp_4318_:
{
size_t v___x_4320_; size_t v___x_4321_; 
v___x_4320_ = ((size_t)1ULL);
v___x_4321_ = lean_usize_add(v_i_4315_, v___x_4320_);
v_i_4315_ = v___x_4321_;
v_b_4317_ = v___y_4319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4327_, lean_object* v_i_4328_, lean_object* v_stop_4329_, lean_object* v_b_4330_){
_start:
{
size_t v_i_boxed_4331_; size_t v_stop_boxed_4332_; lean_object* v_res_4333_; 
v_i_boxed_4331_ = lean_unbox_usize(v_i_4328_);
lean_dec(v_i_4328_);
v_stop_boxed_4332_ = lean_unbox_usize(v_stop_4329_);
lean_dec(v_stop_4329_);
v_res_4333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4327_, v_i_boxed_4331_, v_stop_boxed_4332_, v_b_4330_);
lean_dec_ref(v_as_4327_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4334_, size_t v_sz_4335_, size_t v_i_4336_, lean_object* v_bs_4337_){
_start:
{
uint8_t v___x_4338_; 
v___x_4338_ = lean_usize_dec_lt(v_i_4336_, v_sz_4335_);
if (v___x_4338_ == 0)
{
return v_bs_4337_;
}
else
{
lean_object* v_v_4339_; lean_object* v___x_4340_; lean_object* v_bs_x27_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v_v_4339_ = lean_array_uget(v_bs_4337_, v_i_4336_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v_bs_x27_4341_ = lean_array_uset(v_bs_4337_, v_i_4336_, v___x_4340_);
v___x_4342_ = l_Lean_Meta_FVarSubst_get(v_fs_4334_, v_v_4339_);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_add(v_i_4336_, v___x_4343_);
v___x_4345_ = lean_array_uset(v_bs_x27_4341_, v_i_4336_, v___x_4342_);
v_i_4336_ = v___x_4344_;
v_bs_4337_ = v___x_4345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4347_, lean_object* v_sz_4348_, lean_object* v_i_4349_, lean_object* v_bs_4350_){
_start:
{
size_t v_sz_boxed_4351_; size_t v_i_boxed_4352_; lean_object* v_res_4353_; 
v_sz_boxed_4351_ = lean_unbox_usize(v_sz_4348_);
lean_dec(v_sz_4348_);
v_i_boxed_4352_ = lean_unbox_usize(v_i_4349_);
lean_dec(v_i_4349_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4347_, v_sz_boxed_4351_, v_i_boxed_4352_, v_bs_4350_);
lean_dec(v_fs_4347_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4354_, size_t v_i_4355_, lean_object* v_bs_4356_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = lean_usize_dec_lt(v_i_4355_, v_sz_4354_);
if (v___x_4357_ == 0)
{
return v_bs_4356_;
}
else
{
lean_object* v_v_4358_; lean_object* v___x_4359_; lean_object* v_bs_x27_4360_; lean_object* v___x_4361_; size_t v___x_4362_; size_t v___x_4363_; lean_object* v___x_4364_; 
v_v_4358_ = lean_array_uget(v_bs_4356_, v_i_4355_);
v___x_4359_ = lean_unsigned_to_nat(0u);
v_bs_x27_4360_ = lean_array_uset(v_bs_4356_, v_i_4355_, v___x_4359_);
v___x_4361_ = l_Lean_Expr_fvarId_x21(v_v_4358_);
lean_dec(v_v_4358_);
v___x_4362_ = ((size_t)1ULL);
v___x_4363_ = lean_usize_add(v_i_4355_, v___x_4362_);
v___x_4364_ = lean_array_uset(v_bs_x27_4360_, v_i_4355_, v___x_4361_);
v_i_4355_ = v___x_4363_;
v_bs_4356_ = v___x_4364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4366_, lean_object* v_i_4367_, lean_object* v_bs_4368_){
_start:
{
size_t v_sz_boxed_4369_; size_t v_i_boxed_4370_; lean_object* v_res_4371_; 
v_sz_boxed_4369_ = lean_unbox_usize(v_sz_4366_);
lean_dec(v_sz_4366_);
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_res_4371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4369_, v_i_boxed_4370_, v_bs_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4376_, lean_object* v_g_4377_, lean_object* v_fs_4378_, lean_object* v_clears_4379_, lean_object* v_gs_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___y_4389_; size_t v_sz_4426_; size_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v_sz_4426_ = lean_array_size(v_clears_4379_);
v___x_4427_ = ((size_t)0ULL);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4378_, v_sz_4426_, v___x_4427_, v_clears_4379_);
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = lean_array_get_size(v___x_4428_);
v___x_4431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4432_ = lean_nat_dec_lt(v___x_4429_, v___x_4430_);
if (v___x_4432_ == 0)
{
lean_dec_ref(v___x_4428_);
v___y_4389_ = v___x_4431_;
goto v___jp_4388_;
}
else
{
size_t v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_usize_of_nat(v___x_4430_);
v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4428_, v___x_4427_, v___x_4433_, v___x_4431_);
lean_dec_ref(v___x_4428_);
v___y_4389_ = v___x_4434_;
goto v___jp_4388_;
}
v___jp_4388_:
{
size_t v_sz_4390_; size_t v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_sz_4390_ = lean_array_size(v___y_4389_);
v___x_4391_ = ((size_t)0ULL);
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4390_, v___x_4391_, v___y_4389_);
v___x_4393_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4377_, v___x_4392_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; size_t v_sz_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___f_4399_; lean_object* v___x_4400_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_n(v_a_4394_, 2);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = lean_box(0);
v_sz_4396_ = lean_array_size(v_toTag_4376_);
v___x_4397_ = lean_box_usize(v_sz_4396_);
v___x_4398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4399_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4399_, 0, v_fs_4378_);
lean_closure_set(v___f_4399_, 1, v_toTag_4376_);
lean_closure_set(v___f_4399_, 2, v___x_4397_);
lean_closure_set(v___f_4399_, 3, v___x_4398_);
lean_closure_set(v___f_4399_, 4, v___x_4395_);
v___x_4400_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4394_, v___f_4399_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4408_; 
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v___x_4400_, 0);
lean_dec(v_unused_4409_);
v___x_4402_ = v___x_4400_;
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
else
{
lean_dec(v___x_4400_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4408_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4404_ = lean_array_push(v_gs_4380_, v_a_4394_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4404_);
v___x_4406_ = v___x_4402_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_a_4394_);
lean_dec_ref(v_gs_4380_);
v_a_4410_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4400_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4400_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v_gs_4380_);
lean_dec(v_fs_4378_);
lean_dec_ref(v_toTag_4376_);
v_a_4418_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4393_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4393_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4435_, lean_object* v_g_4436_, lean_object* v_fs_4437_, lean_object* v_clears_4438_, lean_object* v_gs_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4435_, v_g_4436_, v_fs_4437_, v_clears_4438_, v_gs_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4447_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = lean_box(0);
v___x_4449_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
lean_ctor_set(v___x_4450_, 1, v___x_4448_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4508_);
v___x_4515_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4508_);
v___x_4517_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4508_);
v___x_4519_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4508_);
v___x_4521_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4508_);
v___x_4523_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4508_);
v___x_4525_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4508_);
v___x_4527_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4508_);
v___x_4529_ = l_Lean_Syntax_isOfKind(v_stx_4508_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; 
lean_dec(v_stx_4508_);
v___x_4530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4530_;
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4531_);
v___x_4533_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4532_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4542_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4542_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4542_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4540_; 
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v_stx_4508_);
lean_ctor_set(v___x_4538_, 1, v_a_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4538_);
v___x_4540_ = v___x_4536_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
else
{
lean_dec(v_stx_4508_);
return v___x_4533_;
}
}
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v_ps_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4543_ = lean_unsigned_to_nat(1u);
v___x_4544_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4543_);
v_ps_4545_ = l_Lean_Syntax_getArgs(v___x_4544_);
lean_dec(v___x_4544_);
v___x_4546_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4545_);
lean_dec_ref(v_ps_4545_);
v___x_4547_ = lean_array_to_list(v___x_4546_);
v___x_4548_ = lean_box(0);
v___x_4549_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4547_, v___x_4548_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4558_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4558_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4554_, 0, v_stx_4508_);
lean_ctor_set(v___x_4554_, 1, v_a_4550_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4554_);
v___x_4556_ = v___x_4552_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_stx_4508_);
v_a_4559_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4549_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4549_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = lean_unsigned_to_nat(1u);
v___x_4568_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4567_);
v___x_4569_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4568_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4578_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4574_, 0, v_stx_4508_);
lean_ctor_set(v___x_4574_, 1, v_a_4570_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4574_);
v___x_4576_ = v___x_4572_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
else
{
lean_dec(v_stx_4508_);
return v___x_4569_;
}
}
}
else
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_stx_4508_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
}
else
{
lean_object* v___x_4581_; lean_object* v_h_4582_; lean_object* v___x_4583_; uint8_t v___x_4584_; 
v___x_4581_ = lean_unsigned_to_nat(0u);
v_h_4582_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4581_);
lean_dec(v_stx_4508_);
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4582_);
v___x_4584_ = l_Lean_Syntax_isOfKind(v_h_4582_, v___x_4583_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; 
lean_dec(v_h_4582_);
v___x_4585_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4585_;
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4586_ = l_Lean_TSyntax_getId(v_h_4582_);
v___x_4587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4587_, 0, v_h_4582_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
else
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4590_, 0, v_stx_4508_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
return v___x_4591_;
}
}
else
{
lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4592_ = lean_unsigned_to_nat(0u);
v___x_4593_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4592_);
lean_inc(v___x_4593_);
v___x_4594_ = l_Lean_Syntax_isOfKind(v___x_4593_, v___x_4514_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; 
lean_dec(v___x_4593_);
lean_dec(v_stx_4508_);
v___x_4595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4595_;
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4596_ = lean_unsigned_to_nat(1u);
v___x_4597_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4596_);
v___x_4598_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4597_);
v___x_4599_ = l_Lean_Syntax_matchesNull(v___x_4597_, v___x_4598_);
if (v___x_4599_ == 0)
{
uint8_t v___x_4600_; 
lean_dec(v_stx_4508_);
v___x_4600_ = l_Lean_Syntax_matchesNull(v___x_4597_, v___x_4592_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; 
lean_dec(v___x_4593_);
v___x_4601_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4601_;
}
else
{
v_stx_4508_ = v___x_4593_;
goto _start;
}
}
else
{
lean_object* v_t_4603_; lean_object* v___x_4604_; 
v_t_4603_ = l_Lean_Syntax_getArg(v___x_4597_, v___x_4596_);
lean_dec(v___x_4597_);
v___x_4604_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4593_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4613_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4613_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4609_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4609_, 0, v_stx_4508_);
lean_ctor_set(v___x_4609_, 1, v_a_4605_);
lean_ctor_set(v___x_4609_, 2, v_t_4603_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4609_);
v___x_4611_ = v___x_4607_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
else
{
lean_dec(v_t_4603_);
lean_dec(v_stx_4508_);
return v___x_4604_;
}
}
}
}
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v_ps_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = l_Lean_Syntax_getArg(v_stx_4508_, v___x_4614_);
v_ps_4616_ = l_Lean_Syntax_getArgs(v___x_4615_);
lean_dec(v___x_4615_);
v___x_4617_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4616_);
lean_dec_ref(v_ps_4616_);
v___x_4618_ = lean_array_to_list(v___x_4617_);
v___x_4619_ = lean_box(0);
v___x_4620_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4618_, v___x_4619_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4629_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4629_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4629_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4625_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4508_, v_a_4621_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v___x_4625_);
v___x_4627_ = v___x_4623_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec(v_stx_4508_);
v_a_4630_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4620_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4620_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4638_, lean_object* v_x_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
if (lean_obj_tag(v_x_4638_) == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = l_List_reverse___redArg(v_x_4639_);
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
return v___x_4646_;
}
else
{
lean_object* v_head_4647_; lean_object* v_tail_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4666_; 
v_head_4647_ = lean_ctor_get(v_x_4638_, 0);
v_tail_4648_ = lean_ctor_get(v_x_4638_, 1);
v_isSharedCheck_4666_ = !lean_is_exclusive(v_x_4638_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4650_ = v_x_4638_;
v_isShared_4651_ = v_isSharedCheck_4666_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_tail_4648_);
lean_inc(v_head_4647_);
lean_dec(v_x_4638_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4666_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; 
v___x_4652_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4647_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref_known(v___x_4652_, 1);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 1, v_x_4639_);
lean_ctor_set(v___x_4650_, 0, v_a_4653_);
v___x_4655_ = v___x_4650_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4653_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_x_4639_);
v___x_4655_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
v_x_4638_ = v_tail_4648_;
v_x_4639_ = v___x_4655_;
goto _start;
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_del_object(v___x_4650_);
lean_dec(v_tail_4648_);
lean_dec(v_x_4639_);
v_a_4658_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4652_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4652_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4667_, lean_object* v_x_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4667_, v_x_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4682_, lean_object* v_as_4683_, size_t v_sz_4684_, size_t v_i_4685_, lean_object* v_b_4686_){
_start:
{
lean_object* v_a_4689_; uint8_t v___x_4693_; 
v___x_4693_ = lean_usize_dec_lt(v_i_4685_, v_sz_4684_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_b_4686_);
return v___x_4694_;
}
else
{
lean_object* v_fst_4695_; lean_object* v_snd_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4716_; 
v_fst_4695_ = lean_ctor_get(v_b_4686_, 0);
v_snd_4696_ = lean_ctor_get(v_b_4686_, 1);
v_isSharedCheck_4716_ = !lean_is_exclusive(v_b_4686_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4698_ = v_b_4686_;
v_isShared_4699_ = v_isSharedCheck_4716_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_snd_4696_);
lean_inc(v_fst_4695_);
lean_dec(v_b_4686_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4716_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_a_4700_; lean_object* v_expr_4701_; lean_object* v_hName_x3f_4702_; lean_object* v___x_4703_; uint8_t v___x_4713_; 
v_a_4700_ = lean_array_uget_borrowed(v_as_4683_, v_i_4685_);
v_expr_4701_ = lean_ctor_get(v_a_4700_, 0);
v_hName_x3f_4702_ = lean_ctor_get(v_a_4700_, 2);
v___x_4703_ = lean_box(0);
v___x_4713_ = l_Lean_Expr_isFVar(v_expr_4701_);
if (v___x_4713_ == 0)
{
goto v___jp_4704_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4702_) == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
lean_del_object(v___x_4698_);
lean_inc_ref(v_expr_4701_);
v___x_4714_ = lean_array_push(v_fst_4695_, v_expr_4701_);
v___x_4715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
lean_ctor_set(v___x_4715_, 1, v_snd_4696_);
v_a_4689_ = v___x_4715_;
goto v___jp_4688_;
}
else
{
goto v___jp_4704_;
}
}
v___jp_4704_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4705_ = lean_array_get_borrowed(v___x_4703_, v_fst_4682_, v_snd_4696_);
lean_inc(v___x_4705_);
v___x_4706_ = l_Lean_mkFVar(v___x_4705_);
v___x_4707_ = lean_array_push(v_fst_4695_, v___x_4706_);
v___x_4708_ = lean_unsigned_to_nat(1u);
v___x_4709_ = lean_nat_add(v_snd_4696_, v___x_4708_);
lean_dec(v_snd_4696_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 1, v___x_4709_);
lean_ctor_set(v___x_4698_, 0, v___x_4707_);
v___x_4711_ = v___x_4698_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
v_a_4689_ = v___x_4711_;
goto v___jp_4688_;
}
}
}
}
v___jp_4688_:
{
size_t v___x_4690_; size_t v___x_4691_; 
v___x_4690_ = ((size_t)1ULL);
v___x_4691_ = lean_usize_add(v_i_4685_, v___x_4690_);
v_i_4685_ = v___x_4691_;
v_b_4686_ = v_a_4689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4717_, lean_object* v_as_4718_, lean_object* v_sz_4719_, lean_object* v_i_4720_, lean_object* v_b_4721_, lean_object* v___y_4722_){
_start:
{
size_t v_sz_boxed_4723_; size_t v_i_boxed_4724_; lean_object* v_res_4725_; 
v_sz_boxed_4723_ = lean_unbox_usize(v_sz_4719_);
lean_dec(v_sz_4719_);
v_i_boxed_4724_ = lean_unbox_usize(v_i_4720_);
lean_dec(v_i_4720_);
v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4717_, v_as_4718_, v_sz_boxed_4723_, v_i_boxed_4724_, v_b_4721_);
lean_dec_ref(v_as_4718_);
lean_dec_ref(v_fst_4717_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4726_, size_t v_i_4727_, size_t v_stop_4728_, lean_object* v_b_4729_){
_start:
{
lean_object* v___y_4731_; uint8_t v___x_4735_; 
v___x_4735_ = lean_usize_dec_eq(v_i_4727_, v_stop_4728_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v_expr_4737_; lean_object* v_hName_x3f_4738_; uint8_t v___x_4739_; 
v___x_4736_ = lean_array_uget_borrowed(v_as_4726_, v_i_4727_);
v_expr_4737_ = lean_ctor_get(v___x_4736_, 0);
v_hName_x3f_4738_ = lean_ctor_get(v___x_4736_, 2);
v___x_4739_ = l_Lean_Expr_isFVar(v_expr_4737_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; 
lean_inc(v___x_4736_);
v___x_4740_ = lean_array_push(v_b_4729_, v___x_4736_);
v___y_4731_ = v___x_4740_;
goto v___jp_4730_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4738_) == 0)
{
v___y_4731_ = v_b_4729_;
goto v___jp_4730_;
}
else
{
lean_object* v___x_4741_; 
lean_inc(v___x_4736_);
v___x_4741_ = lean_array_push(v_b_4729_, v___x_4736_);
v___y_4731_ = v___x_4741_;
goto v___jp_4730_;
}
}
}
else
{
return v_b_4729_;
}
v___jp_4730_:
{
size_t v___x_4732_; size_t v___x_4733_; 
v___x_4732_ = ((size_t)1ULL);
v___x_4733_ = lean_usize_add(v_i_4727_, v___x_4732_);
v_i_4727_ = v___x_4733_;
v_b_4729_ = v___y_4731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4742_, lean_object* v_i_4743_, lean_object* v_stop_4744_, lean_object* v_b_4745_){
_start:
{
size_t v_i_boxed_4746_; size_t v_stop_boxed_4747_; lean_object* v_res_4748_; 
v_i_boxed_4746_ = lean_unbox_usize(v_i_4743_);
lean_dec(v_i_4743_);
v_stop_boxed_4747_ = lean_unbox_usize(v_stop_4744_);
lean_dec(v_stop_4744_);
v_res_4748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4742_, v_i_boxed_4746_, v_stop_boxed_4747_, v_b_4745_);
lean_dec_ref(v_as_4742_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4754_, lean_object* v_args_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v_lower_4765_; lean_object* v_upper_4766_; lean_object* v_j_4772_; lean_object* v___y_4774_; lean_object* v___x_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; 
v_j_4772_ = lean_unsigned_to_nat(0u);
v___x_4805_ = lean_array_get_size(v_args_4755_);
v___x_4806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4807_ = lean_nat_dec_lt(v_j_4772_, v___x_4805_);
if (v___x_4807_ == 0)
{
v___y_4774_ = v___x_4806_;
goto v___jp_4773_;
}
else
{
size_t v___x_4808_; size_t v___x_4809_; lean_object* v___x_4810_; 
v___x_4808_ = ((size_t)0ULL);
v___x_4809_ = lean_usize_of_nat(v___x_4805_);
v___x_4810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4755_, v___x_4808_, v___x_4809_, v___x_4806_);
v___y_4774_ = v___x_4810_;
goto v___jp_4773_;
}
v___jp_4761_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4767_ = l_Array_toSubarray___redArg(v___y_4764_, v_lower_4765_, v_upper_4766_);
v___x_4768_ = l_Subarray_copy___redArg(v___x_4767_);
v___x_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
lean_ctor_set(v___x_4769_, 1, v___y_4762_);
v___x_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___y_4763_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
return v___x_4771_;
}
v___jp_4773_:
{
uint8_t v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = 3;
v___x_4776_ = l_Lean_MVarId_generalize(v_goal_4754_, v___y_4774_, v___x_4775_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v_fst_4778_; lean_object* v_snd_4779_; lean_object* v___x_4780_; size_t v_sz_4781_; size_t v___x_4782_; lean_object* v___x_4783_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4776_, 1);
v_fst_4778_ = lean_ctor_get(v_a_4777_, 0);
lean_inc(v_fst_4778_);
v_snd_4779_ = lean_ctor_get(v_a_4777_, 1);
lean_inc(v_snd_4779_);
lean_dec(v_a_4777_);
v___x_4780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4781_ = lean_array_size(v_args_4755_);
v___x_4782_ = ((size_t)0ULL);
v___x_4783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4778_, v_args_4755_, v_sz_4781_, v___x_4782_, v___x_4780_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v_fst_4785_; lean_object* v_snd_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
v_fst_4785_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_fst_4785_);
v_snd_4786_ = lean_ctor_get(v_a_4784_, 1);
lean_inc(v_snd_4786_);
lean_dec(v_a_4784_);
v___x_4787_ = lean_array_get_size(v_fst_4778_);
v___x_4788_ = lean_nat_dec_le(v_snd_4786_, v_j_4772_);
if (v___x_4788_ == 0)
{
v___y_4762_ = v_snd_4779_;
v___y_4763_ = v_fst_4785_;
v___y_4764_ = v_fst_4778_;
v_lower_4765_ = v_snd_4786_;
v_upper_4766_ = v___x_4787_;
goto v___jp_4761_;
}
else
{
lean_dec(v_snd_4786_);
v___y_4762_ = v_snd_4779_;
v___y_4763_ = v_fst_4785_;
v___y_4764_ = v_fst_4778_;
v_lower_4765_ = v_j_4772_;
v_upper_4766_ = v___x_4787_;
goto v___jp_4761_;
}
}
else
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
lean_dec(v_snd_4779_);
lean_dec(v_fst_4778_);
v_a_4789_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4783_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4783_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
v_a_4797_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4776_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4776_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4811_, lean_object* v_args_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4811_, v_args_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec_ref(v_args_4812_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4819_, lean_object* v_as_4820_, size_t v_sz_4821_, size_t v_i_4822_, lean_object* v_b_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4819_, v_as_4820_, v_sz_4821_, v_i_4822_, v_b_4823_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4830_, lean_object* v_as_4831_, lean_object* v_sz_4832_, lean_object* v_i_4833_, lean_object* v_b_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
size_t v_sz_boxed_4840_; size_t v_i_boxed_4841_; lean_object* v_res_4842_; 
v_sz_boxed_4840_ = lean_unbox_usize(v_sz_4832_);
lean_dec(v_sz_4832_);
v_i_boxed_4841_ = lean_unbox_usize(v_i_4833_);
lean_dec(v_i_4833_);
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4830_, v_as_4831_, v_sz_boxed_4840_, v_i_boxed_4841_, v_b_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec_ref(v_as_4831_);
lean_dec_ref(v_fst_4830_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4843_, size_t v_i_4844_, size_t v_stop_4845_, lean_object* v_b_4846_){
_start:
{
lean_object* v___y_4848_; uint8_t v___x_4852_; 
v___x_4852_ = lean_usize_dec_eq(v_i_4844_, v_stop_4845_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v_fst_4854_; 
v___x_4853_ = lean_array_uget_borrowed(v_as_4843_, v_i_4844_);
v_fst_4854_ = lean_ctor_get(v___x_4853_, 0);
if (lean_obj_tag(v_fst_4854_) == 0)
{
v___y_4848_ = v_b_4846_;
goto v___jp_4847_;
}
else
{
lean_object* v_val_4855_; lean_object* v___x_4856_; 
v_val_4855_ = lean_ctor_get(v_fst_4854_, 0);
lean_inc(v_val_4855_);
v___x_4856_ = lean_array_push(v_b_4846_, v_val_4855_);
v___y_4848_ = v___x_4856_;
goto v___jp_4847_;
}
}
else
{
return v_b_4846_;
}
v___jp_4847_:
{
size_t v___x_4849_; size_t v___x_4850_; 
v___x_4849_ = ((size_t)1ULL);
v___x_4850_ = lean_usize_add(v_i_4844_, v___x_4849_);
v_i_4844_ = v___x_4850_;
v_b_4846_ = v___y_4848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4857_, lean_object* v_i_4858_, lean_object* v_stop_4859_, lean_object* v_b_4860_){
_start:
{
size_t v_i_boxed_4861_; size_t v_stop_boxed_4862_; lean_object* v_res_4863_; 
v_i_boxed_4861_ = lean_unbox_usize(v_i_4858_);
lean_dec(v_i_4858_);
v_stop_boxed_4862_ = lean_unbox_usize(v_stop_4859_);
lean_dec(v_stop_4859_);
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4857_, v_i_boxed_4861_, v_stop_boxed_4862_, v_b_4860_);
lean_dec_ref(v_as_4857_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4866_, lean_object* v_start_4867_, lean_object* v_stop_4868_){
_start:
{
lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4869_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4870_ = lean_nat_dec_lt(v_start_4867_, v_stop_4868_);
if (v___x_4870_ == 0)
{
return v___x_4869_;
}
else
{
lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4871_ = lean_array_get_size(v_as_4866_);
v___x_4872_ = lean_nat_dec_le(v_stop_4868_, v___x_4871_);
if (v___x_4872_ == 0)
{
uint8_t v___x_4873_; 
v___x_4873_ = lean_nat_dec_lt(v_start_4867_, v___x_4871_);
if (v___x_4873_ == 0)
{
return v___x_4869_;
}
else
{
size_t v___x_4874_; size_t v___x_4875_; lean_object* v___x_4876_; 
v___x_4874_ = lean_usize_of_nat(v_start_4867_);
v___x_4875_ = lean_usize_of_nat(v___x_4871_);
v___x_4876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4866_, v___x_4874_, v___x_4875_, v___x_4869_);
return v___x_4876_;
}
}
else
{
size_t v___x_4877_; size_t v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = lean_usize_of_nat(v_start_4867_);
v___x_4878_ = lean_usize_of_nat(v_stop_4868_);
v___x_4879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4866_, v___x_4877_, v___x_4878_, v___x_4869_);
return v___x_4879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4880_, lean_object* v_start_4881_, lean_object* v_stop_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4880_, v_start_4881_, v_stop_4882_);
lean_dec(v_stop_4882_);
lean_dec(v_start_4881_);
lean_dec_ref(v_as_4880_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4884_, lean_object* v_bs_4885_, lean_object* v_i_4886_, lean_object* v_cs_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = lean_array_get_size(v_as_4884_);
v___x_4907_ = lean_nat_dec_lt(v_i_4886_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
lean_dec(v_i_4886_);
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v_cs_4887_);
return v___x_4908_;
}
else
{
lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4909_ = lean_array_get_size(v_bs_4885_);
v___x_4910_ = lean_nat_dec_lt(v_i_4886_, v___x_4909_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; 
lean_dec(v_i_4886_);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_cs_4887_);
return v___x_4911_;
}
else
{
lean_object* v_a_4912_; lean_object* v_fst_4913_; lean_object* v_snd_4914_; lean_object* v_fst_4916_; lean_object* v_snd_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v_b_4955_; 
v_a_4912_ = lean_array_fget_borrowed(v_as_4884_, v_i_4886_);
v_fst_4913_ = lean_ctor_get(v_a_4912_, 0);
lean_inc(v_fst_4913_);
v_snd_4914_ = lean_ctor_get(v_a_4912_, 1);
v_b_4955_ = lean_array_fget(v_bs_4885_, v_i_4886_);
if (lean_obj_tag(v_b_4955_) == 4)
{
lean_object* v_ref_4956_; lean_object* v_a_4957_; lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4995_; 
v_ref_4956_ = lean_ctor_get(v_b_4955_, 0);
v_a_4957_ = lean_ctor_get(v_b_4955_, 1);
v_a_4958_ = lean_ctor_get(v_b_4955_, 2);
v_isSharedCheck_4995_ = !lean_is_exclusive(v_b_4955_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4960_ = v_b_4955_;
v_isShared_4961_ = v_isSharedCheck_4995_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_inc(v_a_4957_);
lean_inc(v_ref_4956_);
lean_dec(v_b_4955_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4995_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v_toCold_4962_; lean_object* v_currRecDepth_4963_; lean_object* v_ref_4964_; uint16_t v_optionFlags_4965_; uint8_t v_suppressElabErrors_4966_; uint8_t v_checkDeprecated_4967_; uint8_t v_isRecordingDeps_4968_; lean_object* v_ref_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_toCold_4962_ = lean_ctor_get(v___y_4892_, 0);
v_currRecDepth_4963_ = lean_ctor_get(v___y_4892_, 1);
v_ref_4964_ = lean_ctor_get(v___y_4892_, 2);
v_optionFlags_4965_ = lean_ctor_get_uint16(v___y_4892_, sizeof(void*)*3);
v_suppressElabErrors_4966_ = lean_ctor_get_uint8(v___y_4892_, sizeof(void*)*3 + 2);
v_checkDeprecated_4967_ = lean_ctor_get_uint8(v___y_4892_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4968_ = lean_ctor_get_uint8(v___y_4892_, sizeof(void*)*3 + 4);
v_ref_4969_ = l_Lean_replaceRef(v_ref_4956_, v_ref_4964_);
lean_inc(v_currRecDepth_4963_);
lean_inc_ref(v_toCold_4962_);
v___x_4970_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4970_, 0, v_toCold_4962_);
lean_ctor_set(v___x_4970_, 1, v_currRecDepth_4963_);
lean_ctor_set(v___x_4970_, 2, v_ref_4969_);
lean_ctor_set_uint16(v___x_4970_, sizeof(void*)*3, v_optionFlags_4965_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*3 + 2, v_suppressElabErrors_4966_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*3 + 3, v_checkDeprecated_4967_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*3 + 4, v_isRecordingDeps_4968_);
v___x_4971_ = l_Lean_Elab_Term_elabType(v_a_4958_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___x_4970_, v___y_4893_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4973_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc_n(v_a_4972_, 2);
lean_dec_ref_known(v___x_4971_, 1);
v___x_4973_ = l_Lean_Elab_Term_exprToSyntax(v_a_4972_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___x_4970_, v___y_4893_);
lean_dec_ref_known(v___x_4970_, 3);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 2, v_a_4974_);
v___x_4976_ = v___x_4960_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_ref_4956_);
lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_a_4957_);
lean_ctor_set(v_reuseFailAlloc_4978_, 2, v_a_4974_);
v___x_4976_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4977_, 0, v_a_4972_);
v_fst_4916_ = v___x_4976_;
v_snd_4917_ = v___x_4977_;
v___y_4918_ = v___y_4888_;
v___y_4919_ = v___y_4889_;
v___y_4920_ = v___y_4890_;
v___y_4921_ = v___y_4891_;
v___y_4922_ = v___y_4892_;
v___y_4923_ = v___y_4893_;
goto v___jp_4915_;
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
lean_dec(v_a_4972_);
lean_del_object(v___x_4960_);
lean_dec_ref(v_a_4957_);
lean_dec(v_ref_4956_);
lean_dec(v_fst_4913_);
lean_dec_ref(v_cs_4887_);
lean_dec(v_i_4886_);
v_a_4979_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4973_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4973_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref_known(v___x_4970_, 3);
lean_del_object(v___x_4960_);
lean_dec_ref(v_a_4957_);
lean_dec(v_ref_4956_);
lean_dec(v_fst_4913_);
lean_dec_ref(v_cs_4887_);
lean_dec(v_i_4886_);
v_a_4987_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4971_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4971_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
}
else
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_box(0);
v_fst_4916_ = v_b_4955_;
v_snd_4917_ = v___x_4996_;
v___y_4918_ = v___y_4888_;
v___y_4919_ = v___y_4889_;
v___y_4920_ = v___y_4890_;
v___y_4921_ = v___y_4891_;
v___y_4922_ = v___y_4892_;
v___y_4923_ = v___y_4893_;
goto v___jp_4915_;
}
v___jp_4915_:
{
lean_object* v___x_4924_; 
lean_inc(v_snd_4917_);
lean_inc(v_snd_4914_);
v___x_4924_ = l_Lean_Elab_Term_elabTerm(v_snd_4914_, v_snd_4917_, v___x_4910_, v___x_4910_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v_a_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_a_4925_);
lean_dec_ref_known(v___x_4924_, 1);
v___x_4926_ = lean_box(0);
v___x_4927_ = l_Lean_Elab_Term_ensureHasType(v_snd_4917_, v_a_4925_, v___x_4926_, v___x_4926_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4929_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___x_4927_, 1);
v___x_4929_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4916_);
if (lean_obj_tag(v_fst_4913_) == 0)
{
v___y_4896_ = v_a_4928_;
v___y_4897_ = v_fst_4916_;
v___y_4898_ = v___x_4929_;
v___y_4899_ = v___x_4926_;
goto v___jp_4895_;
}
else
{
lean_object* v_val_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4938_; 
v_val_4930_ = lean_ctor_get(v_fst_4913_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_fst_4913_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4932_ = v_fst_4913_;
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_val_4930_);
lean_dec(v_fst_4913_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4934_ = l_Lean_TSyntax_getId(v_val_4930_);
lean_dec(v_val_4930_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4934_);
v___x_4936_ = v___x_4932_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
v___y_4896_ = v_a_4928_;
v___y_4897_ = v_fst_4916_;
v___y_4898_ = v___x_4929_;
v___y_4899_ = v___x_4936_;
goto v___jp_4895_;
}
}
}
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
lean_dec_ref(v_fst_4916_);
lean_dec(v_fst_4913_);
lean_dec_ref(v_cs_4887_);
lean_dec(v_i_4886_);
v_a_4939_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v___x_4927_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4927_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec(v_snd_4917_);
lean_dec_ref(v_fst_4916_);
lean_dec(v_fst_4913_);
lean_dec_ref(v_cs_4887_);
lean_dec(v_i_4886_);
v_a_4947_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4924_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4924_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
}
v___jp_4895_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4900_, 0, v___y_4896_);
lean_ctor_set(v___x_4900_, 1, v___y_4898_);
lean_ctor_set(v___x_4900_, 2, v___y_4899_);
v___x_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___y_4897_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
v___x_4902_ = lean_unsigned_to_nat(1u);
v___x_4903_ = lean_nat_add(v_i_4886_, v___x_4902_);
lean_dec(v_i_4886_);
v___x_4904_ = lean_array_push(v_cs_4887_, v___x_4901_);
v_i_4886_ = v___x_4903_;
v_cs_4887_ = v___x_4904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_4997_, lean_object* v_bs_4998_, lean_object* v_i_4999_, lean_object* v_cs_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_4997_, v_bs_4998_, v_i_4999_, v_cs_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec_ref(v_bs_4998_);
lean_dec_ref(v_as_4997_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5011_, lean_object* v_g_5012_, lean_object* v_pats_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5021_ = lean_array_mk(v_pats_5013_);
v___x_5022_ = lean_unsigned_to_nat(0u);
v___x_5023_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5024_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5011_, v___x_5021_, v___x_5022_, v___x_5023_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec_ref(v___x_5021_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___x_5026_; lean_object* v_fst_5027_; lean_object* v_snd_5028_; lean_object* v___x_5029_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_5024_, 1);
v___x_5026_ = l_Array_unzip___redArg(v_a_5025_);
lean_dec(v_a_5025_);
v_fst_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_fst_5027_);
v_snd_5028_ = lean_ctor_get(v___x_5026_, 1);
lean_inc(v_snd_5028_);
lean_dec_ref(v___x_5026_);
v___x_5029_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5012_, v_snd_5028_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v_snd_5028_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v_snd_5031_; lean_object* v_fst_5032_; lean_object* v_fst_5033_; lean_object* v_snd_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___x_5029_, 1);
v_snd_5031_ = lean_ctor_get(v_a_5030_, 1);
lean_inc(v_snd_5031_);
v_fst_5032_ = lean_ctor_get(v_a_5030_, 0);
lean_inc(v_fst_5032_);
lean_dec(v_a_5030_);
v_fst_5033_ = lean_ctor_get(v_snd_5031_, 0);
lean_inc(v_fst_5033_);
v_snd_5034_ = lean_ctor_get(v_snd_5031_, 1);
lean_inc(v_snd_5034_);
lean_dec(v_snd_5031_);
v___x_5035_ = lean_array_get_size(v_tgts_5011_);
v___x_5036_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5011_, v___x_5022_, v___x_5035_);
v___x_5037_ = l_Array_zip___redArg(v___x_5036_, v_fst_5033_);
lean_dec(v_fst_5033_);
lean_dec_ref(v___x_5036_);
v___x_5038_ = lean_box(0);
v___x_5039_ = l_Array_zip___redArg(v_fst_5027_, v_fst_5032_);
lean_dec(v_fst_5032_);
lean_dec(v_fst_5027_);
v___x_5040_ = lean_array_to_list(v___x_5039_);
v___x_5041_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5041_, 0, v___x_5037_);
v___x_5042_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5034_, v___x_5038_, v___x_5023_, v___x_5023_, v___x_5040_, v___x_5041_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5051_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5045_ = v___x_5042_;
v_isShared_5046_ = v_isSharedCheck_5051_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5042_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5051_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5047_; lean_object* v___x_5049_; 
v___x_5047_ = lean_array_to_list(v_a_5043_);
if (v_isShared_5046_ == 0)
{
lean_ctor_set(v___x_5045_, 0, v___x_5047_);
v___x_5049_ = v___x_5045_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5047_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
v_a_5052_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_5042_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5042_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_dec(v_fst_5027_);
v_a_5060_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5029_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5029_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v_g_5012_);
v_a_5068_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5024_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5024_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5076_, lean_object* v_g_5077_, lean_object* v_pats_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5076_, v_g_5077_, v_pats_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec_ref(v_tgts_5076_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5087_, size_t v_sz_5088_, size_t v_i_5089_, lean_object* v_bs_5090_){
_start:
{
uint8_t v___x_5091_; 
v___x_5091_ = lean_usize_dec_lt(v_i_5089_, v_sz_5088_);
if (v___x_5091_ == 0)
{
return v_bs_5090_;
}
else
{
lean_object* v___x_5092_; uint8_t v___x_5093_; lean_object* v___x_5094_; lean_object* v_bs_x27_5095_; uint8_t v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; size_t v___x_5099_; size_t v___x_5100_; lean_object* v___x_5101_; 
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = lean_nat_dec_eq(v___x_5087_, v___x_5092_);
v___x_5094_ = lean_unsigned_to_nat(0u);
v_bs_x27_5095_ = lean_array_uset(v_bs_5090_, v_i_5089_, v___x_5094_);
v___x_5096_ = 0;
v___x_5097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_5098_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5098_, 0, v___x_5097_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1, v___x_5096_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 1, v___x_5093_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 2, v___x_5093_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 3, v___x_5093_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 4, v___x_5093_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 5, v___x_5093_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1 + 6, v___x_5093_);
v___x_5099_ = ((size_t)1ULL);
v___x_5100_ = lean_usize_add(v_i_5089_, v___x_5099_);
v___x_5101_ = lean_array_uset(v_bs_x27_5095_, v_i_5089_, v___x_5098_);
v_i_5089_ = v___x_5100_;
v_bs_5090_ = v___x_5101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5103_, lean_object* v_sz_5104_, lean_object* v_i_5105_, lean_object* v_bs_5106_){
_start:
{
size_t v_sz_boxed_5107_; size_t v_i_boxed_5108_; lean_object* v_res_5109_; 
v_sz_boxed_5107_ = lean_unbox_usize(v_sz_5104_);
lean_dec(v_sz_5104_);
v_i_boxed_5108_ = lean_unbox_usize(v_i_5105_);
lean_dec(v_i_5105_);
v_res_5109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5103_, v_sz_boxed_5107_, v_i_boxed_5108_, v_bs_5106_);
lean_dec(v___x_5103_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5110_, lean_object* v___x_5111_, lean_object* v_pat_5112_, lean_object* v_tgts_5113_, lean_object* v___x_5114_, lean_object* v___f_5115_, lean_object* v_g_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
if (v___x_5110_ == 0)
{
lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___y_5127_; 
lean_dec(v_g_5116_);
v___x_5124_ = lean_unsigned_to_nat(1u);
v___x_5125_ = lean_nat_dec_eq(v___x_5111_, v___x_5124_);
if (v___x_5125_ == 0)
{
lean_object* v_ref_5136_; 
v_ref_5136_ = lean_ctor_get(v_pat_5112_, 0);
lean_inc(v_ref_5136_);
v___y_5127_ = v_ref_5136_;
goto v___jp_5126_;
}
else
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
lean_dec_ref(v_tgts_5113_);
v___x_5137_ = lean_box(0);
v___x_5138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5138_, 0, v_pat_5112_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
lean_inc(v___y_5122_);
lean_inc_ref(v___y_5121_);
lean_inc(v___y_5120_);
lean_inc_ref(v___y_5119_);
lean_inc(v___y_5118_);
lean_inc_ref(v___y_5117_);
v___x_5139_ = lean_apply_8(v___f_5115_, v___x_5138_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, lean_box(0));
return v___x_5139_;
}
v___jp_5126_:
{
lean_object* v___x_5128_; lean_object* v_snd_5129_; size_t v_sz_5130_; size_t v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v_snd_5134_; lean_object* v___x_5135_; 
v___x_5128_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5112_);
v_snd_5129_ = lean_ctor_get(v___x_5128_, 1);
lean_inc(v_snd_5129_);
lean_dec_ref(v___x_5128_);
v_sz_5130_ = lean_array_size(v_tgts_5113_);
v___x_5131_ = ((size_t)0ULL);
v___x_5132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5111_, v_sz_5130_, v___x_5131_, v_tgts_5113_);
v___x_5133_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5127_, v___x_5132_, v___x_5125_, v___x_5114_, v_snd_5129_);
lean_dec_ref(v___x_5132_);
v_snd_5134_ = lean_ctor_get(v___x_5133_, 1);
lean_inc(v_snd_5134_);
lean_dec_ref(v___x_5133_);
lean_inc(v___y_5122_);
lean_inc_ref(v___y_5121_);
lean_inc(v___y_5120_);
lean_inc_ref(v___y_5119_);
lean_inc(v___y_5118_);
lean_inc_ref(v___y_5117_);
v___x_5135_ = lean_apply_8(v___f_5115_, v_snd_5134_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, lean_box(0));
return v___x_5135_;
}
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
lean_dec_ref(v___f_5115_);
lean_dec_ref(v_tgts_5113_);
lean_dec_ref(v_pat_5112_);
v___x_5140_ = lean_box(0);
v___x_5141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5141_, 0, v_g_5116_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
return v___x_5142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5143_, lean_object* v___x_5144_, lean_object* v_pat_5145_, lean_object* v_tgts_5146_, lean_object* v___x_5147_, lean_object* v___f_5148_, lean_object* v_g_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
uint8_t v___x_5055__boxed_5157_; lean_object* v_res_5158_; 
v___x_5055__boxed_5157_ = lean_unbox(v___x_5143_);
v_res_5158_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5055__boxed_5157_, v___x_5144_, v_pat_5145_, v_tgts_5146_, v___x_5147_, v___f_5148_, v_g_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec(v___x_5147_);
lean_dec(v___x_5144_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5159_, lean_object* v_pat_5160_, lean_object* v_g_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v___f_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; lean_object* v___x_5173_; lean_object* v___y_5174_; uint8_t v___x_5175_; lean_object* v___x_5176_; 
lean_inc(v_g_5161_);
lean_inc_ref(v_tgts_5159_);
v___f_5169_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5169_, 0, v_tgts_5159_);
lean_closure_set(v___f_5169_, 1, v_g_5161_);
v___x_5170_ = lean_array_get_size(v_tgts_5159_);
v___x_5171_ = lean_unsigned_to_nat(0u);
v___x_5172_ = lean_nat_dec_eq(v___x_5170_, v___x_5171_);
v___x_5173_ = lean_box(v___x_5172_);
v___y_5174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5174_, 0, v___x_5173_);
lean_closure_set(v___y_5174_, 1, v___x_5170_);
lean_closure_set(v___y_5174_, 2, v_pat_5160_);
lean_closure_set(v___y_5174_, 3, v_tgts_5159_);
lean_closure_set(v___y_5174_, 4, v___x_5171_);
lean_closure_set(v___y_5174_, 5, v___f_5169_);
lean_closure_set(v___y_5174_, 6, v_g_5161_);
v___x_5175_ = 1;
v___x_5176_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5174_, v___x_5175_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5177_, lean_object* v_pat_5178_, lean_object* v_g_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5177_, v_pat_5178_, v_g_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
lean_dec(v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec(v_a_5183_);
lean_dec_ref(v_a_5182_);
lean_dec(v_a_5181_);
lean_dec_ref(v_a_5180_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5192_, lean_object* v_g_5193_, lean_object* v_pat_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l_Lean_Elab_Term_elabType(v_ty_5192_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; lean_object* v___x_5204_; uint8_t v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
lean_inc_n(v_a_5203_, 2);
lean_dec_ref_known(v___x_5202_, 1);
v___x_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5204_, 0, v_a_5203_);
v___x_5205_ = 0;
v___x_5206_ = lean_box(0);
v___x_5207_ = l_Lean_Meta_mkFreshExprMVar(v___x_5204_, v___x_5205_, v___x_5206_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v___y_5210_; lean_object* v___x_5264_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v___x_5264_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5194_);
if (lean_obj_tag(v___x_5264_) == 0)
{
v___y_5210_ = v___x_5206_;
goto v___jp_5209_;
}
else
{
lean_object* v_val_5265_; 
v_val_5265_ = lean_ctor_get(v___x_5264_, 0);
lean_inc(v_val_5265_);
lean_dec_ref_known(v___x_5264_, 1);
v___y_5210_ = v_val_5265_;
goto v___jp_5209_;
}
v___jp_5209_:
{
lean_object* v___x_5211_; 
lean_inc(v_a_5208_);
v___x_5211_ = l_Lean_MVarId_assert(v_g_5193_, v___y_5210_, v_a_5203_, v_a_5208_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
lean_inc(v_a_5212_);
lean_dec_ref_known(v___x_5211_, 1);
v___x_5213_ = 0;
v___x_5214_ = l_Lean_Meta_intro1Core(v_a_5212_, v___x_5213_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
if (lean_obj_tag(v___x_5214_) == 0)
{
lean_object* v_a_5215_; lean_object* v_fst_5216_; lean_object* v_snd_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5247_; 
v_a_5215_ = lean_ctor_get(v___x_5214_, 0);
lean_inc(v_a_5215_);
lean_dec_ref_known(v___x_5214_, 1);
v_fst_5216_ = lean_ctor_get(v_a_5215_, 0);
v_snd_5217_ = lean_ctor_get(v_a_5215_, 1);
v_isSharedCheck_5247_ = !lean_is_exclusive(v_a_5215_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5219_ = v_a_5215_;
v_isShared_5220_ = v_isSharedCheck_5247_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_snd_5217_);
lean_inc(v_fst_5216_);
lean_dec(v_a_5215_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5247_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5221_ = lean_box(0);
v___x_5222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5223_ = l_Lean_Expr_fvar___override(v_fst_5216_);
v___x_5224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5225_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5217_, v___x_5221_, v___x_5222_, v___x_5223_, v___x_5222_, v_pat_5194_, v___x_5224_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec_ref(v___x_5223_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5238_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5238_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5238_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5233_; 
v___x_5230_ = l_Lean_Expr_mvarId_x21(v_a_5208_);
lean_dec(v_a_5208_);
v___x_5231_ = lean_array_to_list(v_a_5226_);
if (v_isShared_5220_ == 0)
{
lean_ctor_set_tag(v___x_5219_, 1);
lean_ctor_set(v___x_5219_, 1, v___x_5231_);
lean_ctor_set(v___x_5219_, 0, v___x_5230_);
v___x_5233_ = v___x_5219_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5230_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v___x_5231_);
v___x_5233_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
lean_object* v___x_5235_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v___x_5233_);
v___x_5235_ = v___x_5228_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_del_object(v___x_5219_);
lean_dec(v_a_5208_);
v_a_5239_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5225_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5225_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec(v_a_5208_);
lean_dec_ref(v_pat_5194_);
v_a_5248_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5214_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5214_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec(v_a_5208_);
lean_dec_ref(v_pat_5194_);
v_a_5256_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5211_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5211_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec(v_a_5203_);
lean_dec_ref(v_pat_5194_);
lean_dec(v_g_5193_);
v_a_5266_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5207_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5207_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref(v_pat_5194_);
lean_dec(v_g_5193_);
v_a_5274_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5202_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5202_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5282_, lean_object* v_g_5283_, lean_object* v_pat_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5282_, v_g_5283_, v_pat_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5293_, lean_object* v_ty_5294_, lean_object* v_g_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v___f_5303_; uint8_t v___x_5304_; lean_object* v___x_5305_; 
v___f_5303_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5303_, 0, v_ty_5294_);
lean_closure_set(v___f_5303_, 1, v_g_5295_);
lean_closure_set(v___f_5303_, 2, v_pat_5293_);
v___x_5304_ = 1;
v___x_5305_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5303_, v___x_5304_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_);
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5306_, lean_object* v_ty_5307_, lean_object* v_g_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5306_, v_ty_5307_, v_g_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_);
lean_dec(v_a_5314_);
lean_dec_ref(v_a_5313_);
lean_dec(v_a_5312_);
lean_dec_ref(v_a_5311_);
lean_dec(v_a_5310_);
lean_dec_ref(v_a_5309_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5327_, lean_object* v_acc_5328_, lean_object* v_ty_x3f_5329_){
_start:
{
lean_object* v___x_5330_; uint8_t v___x_5331_; 
v___x_5330_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5327_);
v___x_5331_ = l_Lean_Syntax_isOfKind(v_pat_5327_, v___x_5330_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; uint8_t v___x_5333_; 
v___x_5332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5327_);
v___x_5333_ = l_Lean_Syntax_isOfKind(v_pat_5327_, v___x_5332_);
if (v___x_5333_ == 0)
{
lean_dec(v_ty_x3f_5329_);
lean_dec(v_pat_5327_);
return v_acc_5328_;
}
else
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; 
v___x_5334_ = lean_unsigned_to_nat(1u);
v___x_5335_ = l_Lean_Syntax_getArg(v_pat_5327_, v___x_5334_);
v___x_5336_ = lean_unsigned_to_nat(2u);
v___x_5337_ = l_Lean_Syntax_getArg(v_pat_5327_, v___x_5336_);
lean_dec(v_pat_5327_);
v___x_5338_ = l_Lean_Syntax_isNone(v___x_5337_);
if (v___x_5338_ == 0)
{
uint8_t v___x_5339_; 
lean_dec(v_ty_x3f_5329_);
lean_inc(v___x_5337_);
v___x_5339_ = l_Lean_Syntax_matchesNull(v___x_5337_, v___x_5336_);
if (v___x_5339_ == 0)
{
lean_dec(v___x_5337_);
lean_dec(v___x_5335_);
return v_acc_5328_;
}
else
{
lean_object* v_ty_x3f_x27_5340_; lean_object* v___x_5341_; lean_object* v_pats_5342_; lean_object* v___x_5343_; 
v_ty_x3f_x27_5340_ = l_Lean_Syntax_getArg(v___x_5337_, v___x_5334_);
lean_dec(v___x_5337_);
v___x_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5341_, 0, v_ty_x3f_x27_5340_);
v_pats_5342_ = l_Lean_Syntax_getArgs(v___x_5335_);
lean_dec(v___x_5335_);
v___x_5343_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5342_, v_acc_5328_, v___x_5341_);
lean_dec_ref(v_pats_5342_);
return v___x_5343_;
}
}
else
{
lean_object* v_pats_5344_; lean_object* v___x_5345_; 
lean_dec(v___x_5337_);
v_pats_5344_ = l_Lean_Syntax_getArgs(v___x_5335_);
lean_dec(v___x_5335_);
v___x_5345_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5344_, v_acc_5328_, v_ty_x3f_5329_);
lean_dec_ref(v_pats_5344_);
return v___x_5345_;
}
}
}
else
{
lean_object* v___x_5346_; lean_object* v_p_5347_; 
v___x_5346_ = lean_unsigned_to_nat(0u);
v_p_5347_ = l_Lean_Syntax_getArg(v_pat_5327_, v___x_5346_);
lean_dec(v_pat_5327_);
if (lean_obj_tag(v_ty_x3f_5329_) == 0)
{
lean_object* v___x_5348_; 
v___x_5348_ = lean_array_push(v_acc_5328_, v_p_5347_);
return v___x_5348_;
}
else
{
lean_object* v_val_5349_; lean_object* v___x_5350_; lean_object* v_ref_5351_; uint8_t v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; 
v_val_5349_ = lean_ctor_get(v_ty_x3f_5329_, 0);
lean_inc(v_val_5349_);
lean_dec_ref_known(v_ty_x3f_5329_, 1);
v___x_5350_ = lean_box(0);
v_ref_5351_ = l_Lean_replaceRef(v_p_5347_, v___x_5350_);
v___x_5352_ = 0;
v___x_5353_ = l_Lean_SourceInfo_fromRef(v_ref_5351_, v___x_5352_);
lean_dec(v_ref_5351_);
v___x_5354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5353_, 7);
v___x_5356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5353_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5358_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5359_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5360_ = l_Lean_Syntax_node1(v___x_5353_, v___x_5359_, v_p_5347_);
v___x_5361_ = l_Lean_Syntax_node1(v___x_5353_, v___x_5358_, v___x_5360_);
v___x_5362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5353_);
lean_ctor_set(v___x_5363_, 1, v___x_5362_);
v___x_5364_ = l_Lean_Syntax_node2(v___x_5353_, v___x_5359_, v___x_5363_, v_val_5349_);
v___x_5365_ = l_Lean_Syntax_node2(v___x_5353_, v___x_5357_, v___x_5361_, v___x_5364_);
v___x_5366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5353_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = l_Lean_Syntax_node3(v___x_5353_, v___x_5354_, v___x_5356_, v___x_5365_, v___x_5367_);
v___x_5369_ = lean_array_push(v_acc_5328_, v___x_5368_);
return v___x_5369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5370_, lean_object* v_as_5371_, size_t v_i_5372_, size_t v_stop_5373_, lean_object* v_b_5374_){
_start:
{
uint8_t v___x_5375_; 
v___x_5375_ = lean_usize_dec_eq(v_i_5372_, v_stop_5373_);
if (v___x_5375_ == 0)
{
lean_object* v___x_5376_; lean_object* v___x_5377_; size_t v___x_5378_; size_t v___x_5379_; 
v___x_5376_ = lean_array_uget_borrowed(v_as_5371_, v_i_5372_);
lean_inc(v_ty_x3f_5370_);
lean_inc(v___x_5376_);
v___x_5377_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5376_, v_b_5374_, v_ty_x3f_5370_);
v___x_5378_ = ((size_t)1ULL);
v___x_5379_ = lean_usize_add(v_i_5372_, v___x_5378_);
v_i_5372_ = v___x_5379_;
v_b_5374_ = v___x_5377_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5370_);
return v_b_5374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5381_, lean_object* v_acc_5382_, lean_object* v_ty_x3f_5383_){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5384_ = lean_unsigned_to_nat(0u);
v___x_5385_ = lean_array_get_size(v_pats_5381_);
v___x_5386_ = lean_nat_dec_lt(v___x_5384_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_dec(v_ty_x3f_5383_);
return v_acc_5382_;
}
else
{
size_t v___x_5387_; size_t v___x_5388_; lean_object* v___x_5389_; 
v___x_5387_ = ((size_t)0ULL);
v___x_5388_ = lean_usize_of_nat(v___x_5385_);
v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5383_, v_pats_5381_, v___x_5387_, v___x_5388_, v_acc_5382_);
return v___x_5389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5390_, lean_object* v_acc_5391_, lean_object* v_ty_x3f_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5390_, v_acc_5391_, v_ty_x3f_5392_);
lean_dec_ref(v_pats_5390_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5394_, lean_object* v_as_5395_, lean_object* v_i_5396_, lean_object* v_stop_5397_, lean_object* v_b_5398_){
_start:
{
size_t v_i_boxed_5399_; size_t v_stop_boxed_5400_; lean_object* v_res_5401_; 
v_i_boxed_5399_ = lean_unbox_usize(v_i_5396_);
lean_dec(v_i_5396_);
v_stop_boxed_5400_ = lean_unbox_usize(v_stop_5397_);
lean_dec(v_stop_5397_);
v_res_5401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5394_, v_as_5395_, v_i_boxed_5399_, v_stop_boxed_5400_, v_b_5398_);
lean_dec_ref(v_as_5395_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5404_, 0, v___x_5403_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5407_, lean_object* v_pats_5408_, lean_object* v_ty_x3f_5409_, lean_object* v_cont_5410_, lean_object* v_i_5411_, lean_object* v_g_5412_, lean_object* v_fs_5413_, lean_object* v_clears_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5407_, v_pats_5408_, v_ty_x3f_5409_, v_cont_5410_, v_i_5411_, v_g_5412_, v_fs_5413_, v_clears_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
lean_dec(v_i_5411_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5424_ = _args[0];
lean_object* v_ref_5425_ = _args[1];
lean_object* v_pats_5426_ = _args[2];
lean_object* v_ty_x3f_5427_ = _args[3];
lean_object* v_cont_5428_ = _args[4];
lean_object* v_i_5429_ = _args[5];
lean_object* v_g_5430_ = _args[6];
lean_object* v_fs_5431_ = _args[7];
lean_object* v_clears_5432_ = _args[8];
lean_object* v_a_5433_ = _args[9];
lean_object* v_a_5434_ = _args[10];
lean_object* v_a_5435_ = _args[11];
lean_object* v_a_5436_ = _args[12];
lean_object* v_a_5437_ = _args[13];
lean_object* v_a_5438_ = _args[14];
lean_object* v_a_5439_ = _args[15];
lean_object* v_a_5440_ = _args[16];
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5424_, v_ref_5425_, v_pats_5426_, v_ty_x3f_5427_, v_cont_5428_, v_i_5429_, v_g_5430_, v_fs_5431_, v_clears_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
lean_dec(v_i_5429_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5442_, lean_object* v_fs_5443_, lean_object* v_clears_5444_, lean_object* v_ref_5445_, lean_object* v_pats_5446_, lean_object* v_ty_x3f_5447_, lean_object* v_a_5448_, lean_object* v_cont_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_){
_start:
{
lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5457_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5442_);
v___x_5458_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5458_, 0, lean_box(0));
lean_closure_set(v___x_5458_, 1, v_ref_5445_);
lean_closure_set(v___x_5458_, 2, v_pats_5446_);
lean_closure_set(v___x_5458_, 3, v_ty_x3f_5447_);
lean_closure_set(v___x_5458_, 4, v_cont_5449_);
lean_closure_set(v___x_5458_, 5, v___x_5457_);
lean_closure_set(v___x_5458_, 6, v_g_5442_);
lean_closure_set(v___x_5458_, 7, v_fs_5443_);
lean_closure_set(v___x_5458_, 8, v_clears_5444_);
lean_closure_set(v___x_5458_, 9, v_a_5448_);
v___x_5459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5442_, v___x_5458_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5460_, lean_object* v_fs_5461_, lean_object* v_clears_5462_, lean_object* v_a_5463_, lean_object* v_ref_5464_, lean_object* v_pat_5465_, lean_object* v_ty_x3f_5466_, lean_object* v_cont_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_){
_start:
{
lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___x_5487_; uint8_t v___x_5488_; 
v___x_5487_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5465_);
v___x_5488_ = l_Lean_Syntax_isOfKind(v_pat_5465_, v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; uint8_t v___x_5490_; 
lean_dec(v_ref_5464_);
v___x_5489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5465_);
v___x_5490_ = l_Lean_Syntax_isOfKind(v_pat_5465_, v___x_5489_);
if (v___x_5490_ == 0)
{
lean_object* v___x_5491_; 
lean_dec_ref(v_cont_5467_);
lean_dec(v_ty_x3f_5466_);
lean_dec(v_pat_5465_);
lean_dec(v_a_5463_);
lean_dec_ref(v_clears_5462_);
lean_dec(v_fs_5461_);
lean_dec(v_g_5460_);
v___x_5491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5491_;
}
else
{
lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v_ty_x3f_x27_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___x_5506_; lean_object* v___x_5507_; uint8_t v___x_5508_; 
v___x_5492_ = lean_unsigned_to_nat(1u);
v___x_5493_ = l_Lean_Syntax_getArg(v_pat_5465_, v___x_5492_);
v___x_5506_ = lean_unsigned_to_nat(2u);
v___x_5507_ = l_Lean_Syntax_getArg(v_pat_5465_, v___x_5506_);
v___x_5508_ = l_Lean_Syntax_isNone(v___x_5507_);
if (v___x_5508_ == 0)
{
uint8_t v___x_5509_; 
lean_inc(v___x_5507_);
v___x_5509_ = l_Lean_Syntax_matchesNull(v___x_5507_, v___x_5506_);
if (v___x_5509_ == 0)
{
lean_object* v___x_5510_; 
lean_dec(v___x_5507_);
lean_dec(v___x_5493_);
lean_dec_ref(v_cont_5467_);
lean_dec(v_ty_x3f_5466_);
lean_dec(v_pat_5465_);
lean_dec(v_a_5463_);
lean_dec_ref(v_clears_5462_);
lean_dec(v_fs_5461_);
lean_dec(v_g_5460_);
v___x_5510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5510_;
}
else
{
lean_object* v_ty_x3f_x27_5511_; lean_object* v___x_5512_; 
v_ty_x3f_x27_5511_ = l_Lean_Syntax_getArg(v___x_5507_, v___x_5492_);
lean_dec(v___x_5507_);
v___x_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5512_, 0, v_ty_x3f_x27_5511_);
v_ty_x3f_x27_5495_ = v___x_5512_;
v___y_5496_ = v_a_5468_;
v___y_5497_ = v_a_5469_;
v___y_5498_ = v_a_5470_;
v___y_5499_ = v_a_5471_;
v___y_5500_ = v_a_5472_;
v___y_5501_ = v_a_5473_;
goto v___jp_5494_;
}
}
else
{
lean_object* v___x_5513_; 
lean_dec(v___x_5507_);
v___x_5513_ = lean_box(0);
v_ty_x3f_x27_5495_ = v___x_5513_;
v___y_5496_ = v_a_5468_;
v___y_5497_ = v_a_5469_;
v___y_5498_ = v_a_5470_;
v___y_5499_ = v_a_5471_;
v___y_5500_ = v_a_5472_;
v___y_5501_ = v_a_5473_;
goto v___jp_5494_;
}
v___jp_5494_:
{
lean_object* v_pats_5502_; lean_object* v___x_5503_; uint8_t v___x_5504_; 
v_pats_5502_ = l_Lean_Syntax_getArgs(v___x_5493_);
lean_dec(v___x_5493_);
v___x_5503_ = lean_array_get_size(v_pats_5502_);
v___x_5504_ = lean_nat_dec_eq(v___x_5503_, v___x_5492_);
if (v___x_5504_ == 0)
{
lean_object* v___x_5505_; 
lean_dec(v_pat_5465_);
v___x_5505_ = lean_box(0);
v___y_5476_ = v_pats_5502_;
v___y_5477_ = v_ty_x3f_x27_5495_;
v___y_5478_ = v___y_5501_;
v___y_5479_ = v___y_5498_;
v___y_5480_ = v___y_5496_;
v___y_5481_ = v___y_5497_;
v___y_5482_ = v___y_5500_;
v___y_5483_ = v___y_5499_;
v___y_5484_ = v___x_5505_;
goto v___jp_5475_;
}
else
{
v___y_5476_ = v_pats_5502_;
v___y_5477_ = v_ty_x3f_x27_5495_;
v___y_5478_ = v___y_5501_;
v___y_5479_ = v___y_5498_;
v___y_5480_ = v___y_5496_;
v___y_5481_ = v___y_5497_;
v___y_5482_ = v___y_5500_;
v___y_5483_ = v___y_5499_;
v___y_5484_ = v_pat_5465_;
goto v___jp_5475_;
}
}
}
}
else
{
lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5514_ = lean_unsigned_to_nat(0u);
v___x_5515_ = l_Lean_Syntax_getArg(v_pat_5465_, v___x_5514_);
lean_dec(v_pat_5465_);
v___x_5516_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5515_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v___x_5518_; lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5546_; lean_object* v_ref_5550_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v___x_5516_, 1);
v___x_5518_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5464_, v_a_5517_, v_ty_x3f_5466_);
lean_dec(v_ty_x3f_5466_);
v_ref_5550_ = lean_ctor_get(v___x_5518_, 0);
lean_inc(v_ref_5550_);
v___y_5546_ = v_ref_5550_;
goto v___jp_5545_;
v___jp_5519_:
{
lean_object* v_toCold_5522_; lean_object* v_currRecDepth_5523_; lean_object* v_ref_5524_; uint16_t v_optionFlags_5525_; uint8_t v_suppressElabErrors_5526_; uint8_t v_checkDeprecated_5527_; uint8_t v_isRecordingDeps_5528_; lean_object* v_ref_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v_toCold_5522_ = lean_ctor_get(v_a_5472_, 0);
v_currRecDepth_5523_ = lean_ctor_get(v_a_5472_, 1);
v_ref_5524_ = lean_ctor_get(v_a_5472_, 2);
v_optionFlags_5525_ = lean_ctor_get_uint16(v_a_5472_, sizeof(void*)*3);
v_suppressElabErrors_5526_ = lean_ctor_get_uint8(v_a_5472_, sizeof(void*)*3 + 2);
v_checkDeprecated_5527_ = lean_ctor_get_uint8(v_a_5472_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5528_ = lean_ctor_get_uint8(v_a_5472_, sizeof(void*)*3 + 4);
v_ref_5529_ = l_Lean_replaceRef(v___y_5520_, v_ref_5524_);
lean_dec(v___y_5520_);
lean_inc(v_currRecDepth_5523_);
lean_inc_ref(v_toCold_5522_);
v___x_5530_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5530_, 0, v_toCold_5522_);
lean_ctor_set(v___x_5530_, 1, v_currRecDepth_5523_);
lean_ctor_set(v___x_5530_, 2, v_ref_5529_);
lean_ctor_set_uint16(v___x_5530_, sizeof(void*)*3, v_optionFlags_5525_);
lean_ctor_set_uint8(v___x_5530_, sizeof(void*)*3 + 2, v_suppressElabErrors_5526_);
lean_ctor_set_uint8(v___x_5530_, sizeof(void*)*3 + 3, v_checkDeprecated_5527_);
lean_ctor_set_uint8(v___x_5530_, sizeof(void*)*3 + 4, v_isRecordingDeps_5528_);
v___x_5531_ = l_Lean_MVarId_intro(v_g_5460_, v___y_5521_, v_a_5470_, v_a_5471_, v___x_5530_, v_a_5473_);
lean_dec_ref_known(v___x_5530_, 3);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; lean_object* v_fst_5533_; lean_object* v_snd_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
lean_inc(v_a_5532_);
lean_dec_ref_known(v___x_5531_, 1);
v_fst_5533_ = lean_ctor_get(v_a_5532_, 0);
lean_inc(v_fst_5533_);
v_snd_5534_ = lean_ctor_get(v_a_5532_, 1);
lean_inc(v_snd_5534_);
lean_dec(v_a_5532_);
v___x_5535_ = l_Lean_Expr_fvar___override(v_fst_5533_);
v___x_5536_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5534_, v_fs_5461_, v_clears_5462_, v___x_5535_, v_a_5463_, v___x_5518_, v_cont_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
lean_dec_ref(v___x_5535_);
return v___x_5536_;
}
else
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5544_; 
lean_dec_ref(v___x_5518_);
lean_dec_ref(v_cont_5467_);
lean_dec(v_a_5463_);
lean_dec_ref(v_clears_5462_);
lean_dec(v_fs_5461_);
v_a_5537_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5539_ = v___x_5531_;
v_isShared_5540_ = v_isSharedCheck_5544_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5531_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5544_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
if (v_isShared_5540_ == 0)
{
v___x_5542_ = v___x_5539_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
}
v___jp_5545_:
{
lean_object* v___x_5547_; 
v___x_5547_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5518_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v___x_5548_; 
v___x_5548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5520_ = v___y_5546_;
v___y_5521_ = v___x_5548_;
goto v___jp_5519_;
}
else
{
lean_object* v_val_5549_; 
v_val_5549_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_val_5549_);
lean_dec_ref_known(v___x_5547_, 1);
v___y_5520_ = v___y_5546_;
v___y_5521_ = v_val_5549_;
goto v___jp_5519_;
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec_ref(v_cont_5467_);
lean_dec(v_ty_x3f_5466_);
lean_dec(v_ref_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_clears_5462_);
lean_dec(v_fs_5461_);
lean_dec(v_g_5460_);
v_a_5551_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5516_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5516_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
v___jp_5475_:
{
if (lean_obj_tag(v___y_5477_) == 0)
{
lean_object* v___x_5485_; 
v___x_5485_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5460_, v_fs_5461_, v_clears_5462_, v___y_5484_, v___y_5476_, v_ty_x3f_5466_, v_a_5463_, v_cont_5467_, v___y_5480_, v___y_5481_, v___y_5479_, v___y_5483_, v___y_5482_, v___y_5478_);
return v___x_5485_;
}
else
{
lean_object* v___x_5486_; 
lean_dec(v_ty_x3f_5466_);
v___x_5486_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5460_, v_fs_5461_, v_clears_5462_, v___y_5484_, v___y_5476_, v___y_5477_, v_a_5463_, v_cont_5467_, v___y_5480_, v___y_5481_, v___y_5479_, v___y_5483_, v___y_5482_, v___y_5478_);
return v___x_5486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5559_, lean_object* v_pats_5560_, lean_object* v_ty_x3f_5561_, lean_object* v_cont_5562_, lean_object* v_i_5563_, lean_object* v_g_5564_, lean_object* v_fs_5565_, lean_object* v_clears_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
lean_object* v___x_5575_; uint8_t v___x_5576_; 
v___x_5575_ = lean_array_get_size(v_pats_5560_);
v___x_5576_ = lean_nat_dec_lt(v_i_5563_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; 
lean_dec(v_ty_x3f_5561_);
lean_dec_ref(v_pats_5560_);
lean_dec(v_ref_5559_);
lean_inc(v_a_5573_);
lean_inc_ref(v_a_5572_);
lean_inc(v_a_5571_);
lean_inc_ref(v_a_5570_);
lean_inc(v_a_5569_);
lean_inc_ref(v_a_5568_);
v___x_5577_ = lean_apply_11(v_cont_5562_, v_g_5564_, v_fs_5565_, v_clears_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, lean_box(0));
return v___x_5577_;
}
else
{
lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5578_ = lean_array_fget(v_pats_5560_, v_i_5563_);
v___x_5579_ = lean_unsigned_to_nat(1u);
v___x_5580_ = lean_nat_add(v_i_5563_, v___x_5579_);
lean_inc(v_ty_x3f_5561_);
lean_inc(v_ref_5559_);
v___x_5581_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5581_, 0, v_ref_5559_);
lean_closure_set(v___x_5581_, 1, v_pats_5560_);
lean_closure_set(v___x_5581_, 2, v_ty_x3f_5561_);
lean_closure_set(v___x_5581_, 3, v_cont_5562_);
lean_closure_set(v___x_5581_, 4, v___x_5580_);
v___x_5582_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5564_, v_fs_5565_, v_clears_5566_, v_a_5567_, v_ref_5559_, v___x_5578_, v_ty_x3f_5561_, v___x_5581_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_);
return v___x_5582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5583_, lean_object* v_ref_5584_, lean_object* v_pats_5585_, lean_object* v_ty_x3f_5586_, lean_object* v_cont_5587_, lean_object* v_i_5588_, lean_object* v_g_5589_, lean_object* v_fs_5590_, lean_object* v_clears_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_){
_start:
{
lean_object* v___x_5600_; 
v___x_5600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5584_, v_pats_5585_, v_ty_x3f_5586_, v_cont_5587_, v_i_5588_, v_g_5589_, v_fs_5590_, v_clears_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5601_, lean_object* v_fs_5602_, lean_object* v_clears_5603_, lean_object* v_ref_5604_, lean_object* v_pats_5605_, lean_object* v_ty_x3f_5606_, lean_object* v_a_5607_, lean_object* v_cont_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_){
_start:
{
lean_object* v_res_5616_; 
v_res_5616_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5601_, v_fs_5602_, v_clears_5603_, v_ref_5604_, v_pats_5605_, v_ty_x3f_5606_, v_a_5607_, v_cont_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_);
lean_dec(v_a_5614_);
lean_dec_ref(v_a_5613_);
lean_dec(v_a_5612_);
lean_dec_ref(v_a_5611_);
lean_dec(v_a_5610_);
lean_dec_ref(v_a_5609_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5617_, lean_object* v_fs_5618_, lean_object* v_clears_5619_, lean_object* v_a_5620_, lean_object* v_ref_5621_, lean_object* v_pat_5622_, lean_object* v_ty_x3f_5623_, lean_object* v_cont_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5617_, v_fs_5618_, v_clears_5619_, v_a_5620_, v_ref_5621_, v_pat_5622_, v_ty_x3f_5623_, v_cont_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_);
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
lean_dec(v_a_5628_);
lean_dec_ref(v_a_5627_);
lean_dec(v_a_5626_);
lean_dec_ref(v_a_5625_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v___x_5641_; 
v___x_5641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_){
_start:
{
lean_object* v_res_5650_; 
v_res_5650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
lean_dec(v___y_5648_);
lean_dec_ref(v___y_5647_);
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
return v_res_5650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5651_, lean_object* v_g_5652_, lean_object* v_fs_5653_, lean_object* v_clears_5654_, lean_object* v_a_5655_, lean_object* v_ref_5656_, lean_object* v_pat_5657_, lean_object* v_ty_x3f_5658_, lean_object* v_cont_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_){
_start:
{
lean_object* v___x_5667_; 
v___x_5667_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5652_, v_fs_5653_, v_clears_5654_, v_a_5655_, v_ref_5656_, v_pat_5657_, v_ty_x3f_5658_, v_cont_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_);
return v___x_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5668_, lean_object* v_g_5669_, lean_object* v_fs_5670_, lean_object* v_clears_5671_, lean_object* v_a_5672_, lean_object* v_ref_5673_, lean_object* v_pat_5674_, lean_object* v_ty_x3f_5675_, lean_object* v_cont_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
lean_object* v_res_5684_; 
v_res_5684_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5668_, v_g_5669_, v_fs_5670_, v_clears_5671_, v_a_5672_, v_ref_5673_, v_pat_5674_, v_ty_x3f_5675_, v_cont_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
lean_dec(v_a_5682_);
lean_dec_ref(v_a_5681_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
lean_dec(v_a_5678_);
lean_dec_ref(v_a_5677_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5685_, lean_object* v_g_5686_, lean_object* v_fs_5687_, lean_object* v_clears_5688_, lean_object* v_ref_5689_, lean_object* v_pats_5690_, lean_object* v_ty_x3f_5691_, lean_object* v_a_5692_, lean_object* v_cont_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5686_, v_fs_5687_, v_clears_5688_, v_ref_5689_, v_pats_5690_, v_ty_x3f_5691_, v_a_5692_, v_cont_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5702_, lean_object* v_g_5703_, lean_object* v_fs_5704_, lean_object* v_clears_5705_, lean_object* v_ref_5706_, lean_object* v_pats_5707_, lean_object* v_ty_x3f_5708_, lean_object* v_a_5709_, lean_object* v_cont_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5702_, v_g_5703_, v_fs_5704_, v_clears_5705_, v_ref_5706_, v_pats_5707_, v_ty_x3f_5708_, v_a_5709_, v_cont_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_);
lean_dec(v_a_5716_);
lean_dec_ref(v_a_5715_);
lean_dec(v_a_5714_);
lean_dec_ref(v_a_5713_);
lean_dec(v_a_5712_);
lean_dec_ref(v_a_5711_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5719_, lean_object* v___x_5720_, lean_object* v___x_5721_, lean_object* v___x_5722_, lean_object* v_pats_5723_, lean_object* v_ty_x3f_5724_, lean_object* v___x_5725_, lean_object* v___x_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
lean_object* v___x_5734_; 
v___x_5734_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5719_, v___x_5720_, v___x_5721_, v___x_5722_, v_pats_5723_, v_ty_x3f_5724_, v___x_5725_, v___x_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; lean_object* v___x_5737_; uint8_t v_isShared_5738_; uint8_t v_isSharedCheck_5743_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5743_ == 0)
{
v___x_5737_ = v___x_5734_;
v_isShared_5738_ = v_isSharedCheck_5743_;
goto v_resetjp_5736_;
}
else
{
lean_inc(v_a_5735_);
lean_dec(v___x_5734_);
v___x_5737_ = lean_box(0);
v_isShared_5738_ = v_isSharedCheck_5743_;
goto v_resetjp_5736_;
}
v_resetjp_5736_:
{
lean_object* v___x_5739_; lean_object* v___x_5741_; 
v___x_5739_ = lean_array_to_list(v_a_5735_);
if (v_isShared_5738_ == 0)
{
lean_ctor_set(v___x_5737_, 0, v___x_5739_);
v___x_5741_ = v___x_5737_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
else
{
lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5751_; 
v_a_5744_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5746_ = v___x_5734_;
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5734_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5749_; 
if (v_isShared_5747_ == 0)
{
v___x_5749_ = v___x_5746_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5752_, lean_object* v___x_5753_, lean_object* v___x_5754_, lean_object* v___x_5755_, lean_object* v_pats_5756_, lean_object* v_ty_x3f_5757_, lean_object* v___x_5758_, lean_object* v___x_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
lean_object* v_res_5767_; 
v_res_5767_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5752_, v___x_5753_, v___x_5754_, v___x_5755_, v_pats_5756_, v_ty_x3f_5757_, v___x_5758_, v___x_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
return v_res_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5768_, lean_object* v_ty_x3f_5769_, lean_object* v_g_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_){
_start:
{
lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___f_5782_; uint8_t v___x_5783_; lean_object* v___x_5784_; 
v___x_5778_ = lean_box(0);
v___x_5779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5780_ = lean_box(0);
v___x_5781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5782_, 0, v_g_5770_);
lean_closure_set(v___f_5782_, 1, v___x_5778_);
lean_closure_set(v___f_5782_, 2, v___x_5779_);
lean_closure_set(v___f_5782_, 3, v___x_5780_);
lean_closure_set(v___f_5782_, 4, v_pats_5768_);
lean_closure_set(v___f_5782_, 5, v_ty_x3f_5769_);
lean_closure_set(v___f_5782_, 6, v___x_5779_);
lean_closure_set(v___f_5782_, 7, v___x_5781_);
v___x_5783_ = 1;
v___x_5784_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5782_, v___x_5783_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5785_, lean_object* v_ty_x3f_5786_, lean_object* v_g_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_){
_start:
{
lean_object* v_res_5795_; 
v_res_5795_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5785_, v_ty_x3f_5786_, v_g_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_);
lean_dec(v_a_5793_);
lean_dec_ref(v_a_5792_);
lean_dec(v_a_5791_);
lean_dec_ref(v_a_5790_);
lean_dec(v_a_5789_);
lean_dec_ref(v_a_5788_);
return v_res_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5797_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5798_, 0, v___x_5797_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_){
_start:
{
lean_object* v___x_5811_; 
v___x_5811_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
return v_res_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_){
_start:
{
lean_object* v___x_5833_; 
lean_inc(v___y_5827_);
lean_inc_ref(v___y_5826_);
lean_inc(v___y_5825_);
lean_inc_ref(v___y_5824_);
v___x_5833_ = lean_apply_9(v_x_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, lean_box(0));
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
return v_res_5844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5845_, lean_object* v_x_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v___f_5856_; lean_object* v___x_5857_; 
lean_inc(v___y_5850_);
lean_inc_ref(v___y_5849_);
lean_inc(v___y_5848_);
lean_inc_ref(v___y_5847_);
v___f_5856_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5856_, 0, v_x_5846_);
lean_closure_set(v___f_5856_, 1, v___y_5847_);
lean_closure_set(v___f_5856_, 2, v___y_5848_);
lean_closure_set(v___f_5856_, 3, v___y_5849_);
lean_closure_set(v___f_5856_, 4, v___y_5850_);
v___x_5857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5845_, v___f_5856_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5857_) == 0)
{
return v___x_5857_;
}
else
{
lean_object* v_a_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5865_; 
v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v___x_5857_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5860_ = v___x_5857_;
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_a_5858_);
lean_dec(v___x_5857_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5863_; 
if (v_isShared_5861_ == 0)
{
v___x_5863_ = v___x_5860_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5858_);
v___x_5863_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
return v___x_5863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5866_, lean_object* v_x_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5866_, v_x_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5878_, lean_object* v_mvarId_5879_, lean_object* v_x_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_){
_start:
{
lean_object* v___x_5890_; 
v___x_5890_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5879_, v_x_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
return v___x_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5891_, lean_object* v_mvarId_5892_, lean_object* v_x_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_){
_start:
{
lean_object* v_res_5903_; 
v_res_5903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5891_, v_mvarId_5892_, v_x_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
lean_dec(v___y_5901_);
lean_dec_ref(v___y_5900_);
lean_dec(v___y_5899_);
lean_dec_ref(v___y_5898_);
lean_dec(v___y_5897_);
lean_dec_ref(v___y_5896_);
lean_dec(v___y_5895_);
lean_dec_ref(v___y_5894_);
return v_res_5903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5904_, lean_object* v_pat_5905_, lean_object* v_a_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_){
_start:
{
lean_object* v___x_5916_; 
v___x_5916_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5904_, v_pat_5905_, v_a_5906_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_);
if (lean_obj_tag(v___x_5916_) == 0)
{
lean_object* v_a_5917_; lean_object* v___x_5918_; 
v_a_5917_ = lean_ctor_get(v___x_5916_, 0);
lean_inc(v_a_5917_);
lean_dec_ref_known(v___x_5916_, 1);
v___x_5918_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5917_, v___y_5908_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_);
return v___x_5918_;
}
else
{
lean_object* v_a_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5926_; 
v_a_5919_ = lean_ctor_get(v___x_5916_, 0);
v_isSharedCheck_5926_ = !lean_is_exclusive(v___x_5916_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5921_ = v___x_5916_;
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_a_5919_);
lean_dec(v___x_5916_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5924_; 
if (v_isShared_5922_ == 0)
{
v___x_5924_ = v___x_5921_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
v___x_5924_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
return v___x_5924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5927_, lean_object* v_pat_5928_, lean_object* v_a_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_){
_start:
{
lean_object* v_res_5939_; 
v_res_5939_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5927_, v_pat_5928_, v_a_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_);
lean_dec(v___y_5937_);
lean_dec_ref(v___y_5936_);
lean_dec(v___y_5935_);
lean_dec_ref(v___y_5934_);
lean_dec(v___y_5933_);
lean_dec_ref(v___y_5932_);
lean_dec(v___y_5931_);
lean_dec_ref(v___y_5930_);
return v_res_5939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5940_, size_t v_i_5941_, lean_object* v_bs_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_){
_start:
{
uint8_t v___x_5947_; 
v___x_5947_ = lean_usize_dec_lt(v_i_5941_, v_sz_5940_);
if (v___x_5947_ == 0)
{
lean_object* v___x_5948_; 
v___x_5948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5948_, 0, v_bs_5942_);
return v___x_5948_;
}
else
{
lean_object* v_v_5949_; lean_object* v___x_5950_; lean_object* v_bs_x27_5951_; lean_object* v___x_5952_; 
v_v_5949_ = lean_array_uget(v_bs_5942_, v_i_5941_);
v___x_5950_ = lean_unsigned_to_nat(0u);
v_bs_x27_5951_ = lean_array_uset(v_bs_5942_, v_i_5941_, v___x_5950_);
v___x_5952_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_5949_, v___y_5943_, v___y_5944_, v___y_5945_);
if (lean_obj_tag(v___x_5952_) == 0)
{
lean_object* v_a_5953_; lean_object* v_hIdent_x3f_5954_; lean_object* v_term_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_5966_; 
v_a_5953_ = lean_ctor_get(v___x_5952_, 0);
lean_inc(v_a_5953_);
lean_dec_ref_known(v___x_5952_, 1);
v_hIdent_x3f_5954_ = lean_ctor_get(v_a_5953_, 0);
v_term_5955_ = lean_ctor_get(v_a_5953_, 1);
v_isSharedCheck_5966_ = !lean_is_exclusive(v_a_5953_);
if (v_isSharedCheck_5966_ == 0)
{
v___x_5957_ = v_a_5953_;
v_isShared_5958_ = v_isSharedCheck_5966_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_term_5955_);
lean_inc(v_hIdent_x3f_5954_);
lean_dec(v_a_5953_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_5966_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v___x_5960_; 
if (v_isShared_5958_ == 0)
{
v___x_5960_ = v___x_5957_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_hIdent_x3f_5954_);
lean_ctor_set(v_reuseFailAlloc_5965_, 1, v_term_5955_);
v___x_5960_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
size_t v___x_5961_; size_t v___x_5962_; lean_object* v___x_5963_; 
v___x_5961_ = ((size_t)1ULL);
v___x_5962_ = lean_usize_add(v_i_5941_, v___x_5961_);
v___x_5963_ = lean_array_uset(v_bs_x27_5951_, v_i_5941_, v___x_5960_);
v_i_5941_ = v___x_5962_;
v_bs_5942_ = v___x_5963_;
goto _start;
}
}
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5974_; 
lean_dec_ref(v_bs_x27_5951_);
v_a_5967_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5969_ = v___x_5952_;
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___x_5952_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
if (v_isShared_5970_ == 0)
{
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
v___x_5972_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
return v___x_5972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_5975_, lean_object* v_i_5976_, lean_object* v_bs_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_){
_start:
{
size_t v_sz_boxed_5982_; size_t v_i_boxed_5983_; lean_object* v_res_5984_; 
v_sz_boxed_5982_ = lean_unbox_usize(v_sz_5975_);
lean_dec(v_sz_5975_);
v_i_boxed_5983_ = lean_unbox_usize(v_i_5976_);
lean_dec(v_i_5976_);
v_res_5984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_5982_, v_i_boxed_5983_, v_bs_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec_ref(v___y_5978_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_){
_start:
{
lean_object* v___y_6002_; lean_object* v_pat_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; lean_object* v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; lean_object* v___y_6009_; lean_object* v___y_6010_; lean_object* v___y_6011_; lean_object* v___x_6037_; uint8_t v___x_6038_; 
v___x_6037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_5991_);
v___x_6038_ = l_Lean_Syntax_isOfKind(v_stx_5991_, v___x_6037_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; 
lean_dec(v_stx_5991_);
v___x_6039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6039_;
}
else
{
lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; uint8_t v___x_6044_; 
v___x_6040_ = lean_unsigned_to_nat(1u);
v___x_6041_ = l_Lean_Syntax_getArg(v_stx_5991_, v___x_6040_);
v___x_6042_ = lean_unsigned_to_nat(2u);
v___x_6043_ = l_Lean_Syntax_getArg(v_stx_5991_, v___x_6042_);
v___x_6044_ = l_Lean_Syntax_isNone(v___x_6043_);
if (v___x_6044_ == 0)
{
uint8_t v___x_6045_; 
lean_dec(v_stx_5991_);
lean_inc(v___x_6043_);
v___x_6045_ = l_Lean_Syntax_matchesNull(v___x_6043_, v___x_6042_);
if (v___x_6045_ == 0)
{
lean_object* v___x_6046_; 
lean_dec(v___x_6043_);
lean_dec(v___x_6041_);
v___x_6046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6046_;
}
else
{
lean_object* v_pat_x3f_6047_; lean_object* v_tgts_6048_; lean_object* v___x_6049_; 
v_pat_x3f_6047_ = l_Lean_Syntax_getArg(v___x_6043_, v___x_6040_);
lean_dec(v___x_6043_);
v_tgts_6048_ = l_Lean_Syntax_getArgs(v___x_6041_);
lean_dec(v___x_6041_);
v___x_6049_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6047_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_);
if (lean_obj_tag(v___x_6049_) == 0)
{
lean_object* v_a_6050_; 
v_a_6050_ = lean_ctor_get(v___x_6049_, 0);
lean_inc(v_a_6050_);
lean_dec_ref_known(v___x_6049_, 1);
v___y_6002_ = v_tgts_6048_;
v_pat_6003_ = v_a_6050_;
v___y_6004_ = v_a_5992_;
v___y_6005_ = v_a_5993_;
v___y_6006_ = v_a_5994_;
v___y_6007_ = v_a_5995_;
v___y_6008_ = v_a_5996_;
v___y_6009_ = v_a_5997_;
v___y_6010_ = v_a_5998_;
v___y_6011_ = v_a_5999_;
goto v___jp_6001_;
}
else
{
lean_object* v_a_6051_; lean_object* v___x_6053_; uint8_t v_isShared_6054_; uint8_t v_isSharedCheck_6058_; 
lean_dec_ref(v_tgts_6048_);
v_a_6051_ = lean_ctor_get(v___x_6049_, 0);
v_isSharedCheck_6058_ = !lean_is_exclusive(v___x_6049_);
if (v_isSharedCheck_6058_ == 0)
{
v___x_6053_ = v___x_6049_;
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
else
{
lean_inc(v_a_6051_);
lean_dec(v___x_6049_);
v___x_6053_ = lean_box(0);
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
v_resetjp_6052_:
{
lean_object* v___x_6056_; 
if (v_isShared_6054_ == 0)
{
v___x_6056_ = v___x_6053_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6057_; 
v_reuseFailAlloc_6057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
v___x_6056_ = v_reuseFailAlloc_6057_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
return v___x_6056_;
}
}
}
}
}
else
{
lean_object* v___x_6059_; lean_object* v_tk_6060_; lean_object* v_tgts_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
lean_dec(v___x_6043_);
v___x_6059_ = lean_unsigned_to_nat(0u);
v_tk_6060_ = l_Lean_Syntax_getArg(v_stx_5991_, v___x_6059_);
lean_dec(v_stx_5991_);
v_tgts_6061_ = l_Lean_Syntax_getArgs(v___x_6041_);
lean_dec(v___x_6041_);
v___x_6062_ = lean_box(0);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v_tk_6060_);
lean_ctor_set(v___x_6063_, 1, v___x_6062_);
v___y_6002_ = v_tgts_6061_;
v_pat_6003_ = v___x_6063_;
v___y_6004_ = v_a_5992_;
v___y_6005_ = v_a_5993_;
v___y_6006_ = v_a_5994_;
v___y_6007_ = v_a_5995_;
v___y_6008_ = v_a_5996_;
v___y_6009_ = v_a_5997_;
v___y_6010_ = v_a_5998_;
v___y_6011_ = v_a_5999_;
goto v___jp_6001_;
}
}
v___jp_6001_:
{
lean_object* v___x_6012_; size_t v_sz_6013_; size_t v___x_6014_; lean_object* v___x_6015_; 
v___x_6012_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6002_);
lean_dec_ref(v___y_6002_);
v_sz_6013_ = lean_array_size(v___x_6012_);
v___x_6014_ = ((size_t)0ULL);
v___x_6015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6013_, v___x_6014_, v___x_6012_, v___y_6008_, v___y_6010_, v___y_6011_);
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6017_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
lean_inc(v_a_6016_);
lean_dec_ref_known(v___x_6015_, 1);
v___x_6017_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6005_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_object* v_a_6018_; lean_object* v___f_6019_; lean_object* v___x_6020_; 
v_a_6018_ = lean_ctor_get(v___x_6017_, 0);
lean_inc_n(v_a_6018_, 2);
lean_dec_ref_known(v___x_6017_, 1);
v___f_6019_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6019_, 0, v_a_6016_);
lean_closure_set(v___f_6019_, 1, v_pat_6003_);
lean_closure_set(v___f_6019_, 2, v_a_6018_);
v___x_6020_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6018_, v___f_6019_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
return v___x_6020_;
}
else
{
lean_object* v_a_6021_; lean_object* v___x_6023_; uint8_t v_isShared_6024_; uint8_t v_isSharedCheck_6028_; 
lean_dec(v_a_6016_);
lean_dec_ref(v_pat_6003_);
v_a_6021_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6028_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6028_ == 0)
{
v___x_6023_ = v___x_6017_;
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
else
{
lean_inc(v_a_6021_);
lean_dec(v___x_6017_);
v___x_6023_ = lean_box(0);
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
v_resetjp_6022_:
{
lean_object* v___x_6026_; 
if (v_isShared_6024_ == 0)
{
v___x_6026_ = v___x_6023_;
goto v_reusejp_6025_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
v___x_6026_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6025_;
}
v_reusejp_6025_:
{
return v___x_6026_;
}
}
}
}
else
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6036_; 
lean_dec_ref(v_pat_6003_);
v_a_6029_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6036_ == 0)
{
v___x_6031_ = v___x_6015_;
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6015_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6034_; 
if (v_isShared_6032_ == 0)
{
v___x_6034_ = v___x_6031_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_a_6029_);
v___x_6034_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
return v___x_6034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_){
_start:
{
lean_object* v_res_6074_; 
v_res_6074_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6064_, v_a_6065_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_, v_a_6070_, v_a_6071_, v_a_6072_);
lean_dec(v_a_6072_);
lean_dec_ref(v_a_6071_);
lean_dec(v_a_6070_);
lean_dec_ref(v_a_6069_);
lean_dec(v_a_6068_);
lean_dec_ref(v_a_6067_);
lean_dec(v_a_6066_);
lean_dec_ref(v_a_6065_);
return v_res_6074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6075_, size_t v_i_6076_, lean_object* v_bs_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_){
_start:
{
lean_object* v___x_6087_; 
v___x_6087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6075_, v_i_6076_, v_bs_6077_, v___y_6082_, v___y_6084_, v___y_6085_);
return v___x_6087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6088_, lean_object* v_i_6089_, lean_object* v_bs_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_){
_start:
{
size_t v_sz_boxed_6100_; size_t v_i_boxed_6101_; lean_object* v_res_6102_; 
v_sz_boxed_6100_ = lean_unbox_usize(v_sz_6088_);
lean_dec(v_sz_6088_);
v_i_boxed_6101_ = lean_unbox_usize(v_i_6089_);
lean_dec(v_i_6089_);
v_res_6102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6100_, v_i_boxed_6101_, v_bs_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v___y_6096_);
lean_dec_ref(v___y_6095_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; 
v___x_6139_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6142_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6143_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6139_, v___x_6140_, v___x_6141_, v___x_6142_);
return v___x_6143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6144_){
_start:
{
lean_object* v_res_6145_; 
v_res_6145_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6146_, lean_object* v___x_6147_, lean_object* v_a_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v___x_6158_; 
v___x_6158_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6146_, v___x_6147_, v_a_6148_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
if (lean_obj_tag(v___x_6158_) == 0)
{
lean_object* v_a_6159_; lean_object* v___x_6160_; 
v_a_6159_ = lean_ctor_get(v___x_6158_, 0);
lean_inc(v_a_6159_);
lean_dec_ref_known(v___x_6158_, 1);
v___x_6160_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6159_, v___y_6150_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
return v___x_6160_;
}
else
{
lean_object* v_a_6161_; lean_object* v___x_6163_; uint8_t v_isShared_6164_; uint8_t v_isSharedCheck_6168_; 
v_a_6161_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6168_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6168_ == 0)
{
v___x_6163_ = v___x_6158_;
v_isShared_6164_ = v_isSharedCheck_6168_;
goto v_resetjp_6162_;
}
else
{
lean_inc(v_a_6161_);
lean_dec(v___x_6158_);
v___x_6163_ = lean_box(0);
v_isShared_6164_ = v_isSharedCheck_6168_;
goto v_resetjp_6162_;
}
v_resetjp_6162_:
{
lean_object* v___x_6166_; 
if (v_isShared_6164_ == 0)
{
v___x_6166_ = v___x_6163_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_a_6161_);
v___x_6166_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6165_;
}
v_reusejp_6165_:
{
return v___x_6166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6169_, lean_object* v___x_6170_, lean_object* v_a_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_){
_start:
{
lean_object* v_res_6181_; 
v_res_6181_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6169_, v___x_6170_, v_a_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
return v_res_6181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6182_, lean_object* v_val_6183_, lean_object* v_a_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_){
_start:
{
lean_object* v___x_6194_; 
v___x_6194_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6182_, v_val_6183_, v_a_6184_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v_a_6195_; lean_object* v___x_6196_; 
v_a_6195_ = lean_ctor_get(v___x_6194_, 0);
lean_inc(v_a_6195_);
lean_dec_ref_known(v___x_6194_, 1);
v___x_6196_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6195_, v___y_6186_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
return v___x_6196_;
}
else
{
lean_object* v_a_6197_; lean_object* v___x_6199_; uint8_t v_isShared_6200_; uint8_t v_isSharedCheck_6204_; 
v_a_6197_ = lean_ctor_get(v___x_6194_, 0);
v_isSharedCheck_6204_ = !lean_is_exclusive(v___x_6194_);
if (v_isSharedCheck_6204_ == 0)
{
v___x_6199_ = v___x_6194_;
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
else
{
lean_inc(v_a_6197_);
lean_dec(v___x_6194_);
v___x_6199_ = lean_box(0);
v_isShared_6200_ = v_isSharedCheck_6204_;
goto v_resetjp_6198_;
}
v_resetjp_6198_:
{
lean_object* v___x_6202_; 
if (v_isShared_6200_ == 0)
{
v___x_6202_ = v___x_6199_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v_a_6197_);
v___x_6202_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
return v___x_6202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6205_, lean_object* v_val_6206_, lean_object* v_a_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6205_, v_val_6206_, v_a_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_, v___y_6215_);
lean_dec(v___y_6215_);
lean_dec_ref(v___y_6214_);
lean_dec(v___y_6213_);
lean_dec_ref(v___y_6212_);
lean_dec(v___y_6211_);
lean_dec_ref(v___y_6210_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_){
_start:
{
lean_object* v_ref_6224_; lean_object* v___x_6225_; lean_object* v_a_6226_; lean_object* v___x_6228_; uint8_t v_isShared_6229_; uint8_t v_isSharedCheck_6234_; 
v_ref_6224_ = lean_ctor_get(v___y_6221_, 2);
v___x_6225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
v_a_6226_ = lean_ctor_get(v___x_6225_, 0);
v_isSharedCheck_6234_ = !lean_is_exclusive(v___x_6225_);
if (v_isSharedCheck_6234_ == 0)
{
v___x_6228_ = v___x_6225_;
v_isShared_6229_ = v_isSharedCheck_6234_;
goto v_resetjp_6227_;
}
else
{
lean_inc(v_a_6226_);
lean_dec(v___x_6225_);
v___x_6228_ = lean_box(0);
v_isShared_6229_ = v_isSharedCheck_6234_;
goto v_resetjp_6227_;
}
v_resetjp_6227_:
{
lean_object* v___x_6230_; lean_object* v___x_6232_; 
lean_inc(v_ref_6224_);
v___x_6230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6230_, 0, v_ref_6224_);
lean_ctor_set(v___x_6230_, 1, v_a_6226_);
if (v_isShared_6229_ == 0)
{
lean_ctor_set_tag(v___x_6228_, 1);
lean_ctor_set(v___x_6228_, 0, v___x_6230_);
v___x_6232_ = v___x_6228_;
goto v_reusejp_6231_;
}
else
{
lean_object* v_reuseFailAlloc_6233_; 
v_reuseFailAlloc_6233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6233_, 0, v___x_6230_);
v___x_6232_ = v_reuseFailAlloc_6233_;
goto v_reusejp_6231_;
}
v_reusejp_6231_:
{
return v___x_6232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_){
_start:
{
lean_object* v_res_6241_; 
v_res_6241_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_);
lean_dec(v___y_6239_);
lean_dec_ref(v___y_6238_);
lean_dec(v___y_6237_);
lean_dec_ref(v___y_6236_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6242_, size_t v_i_6243_, lean_object* v_bs_6244_){
_start:
{
uint8_t v___x_6245_; 
v___x_6245_ = lean_usize_dec_lt(v_i_6243_, v_sz_6242_);
if (v___x_6245_ == 0)
{
return v_bs_6244_;
}
else
{
lean_object* v_v_6246_; lean_object* v___x_6247_; lean_object* v_bs_x27_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; size_t v___x_6251_; size_t v___x_6252_; lean_object* v___x_6253_; 
v_v_6246_ = lean_array_uget(v_bs_6244_, v_i_6243_);
v___x_6247_ = lean_unsigned_to_nat(0u);
v_bs_x27_6248_ = lean_array_uset(v_bs_6244_, v_i_6243_, v___x_6247_);
v___x_6249_ = lean_box(0);
v___x_6250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6250_, 0, v___x_6249_);
lean_ctor_set(v___x_6250_, 1, v_v_6246_);
v___x_6251_ = ((size_t)1ULL);
v___x_6252_ = lean_usize_add(v_i_6243_, v___x_6251_);
v___x_6253_ = lean_array_uset(v_bs_x27_6248_, v_i_6243_, v___x_6250_);
v_i_6243_ = v___x_6252_;
v_bs_6244_ = v___x_6253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6255_, lean_object* v_i_6256_, lean_object* v_bs_6257_){
_start:
{
size_t v_sz_boxed_6258_; size_t v_i_boxed_6259_; lean_object* v_res_6260_; 
v_sz_boxed_6258_ = lean_unbox_usize(v_sz_6255_);
lean_dec(v_sz_6255_);
v_i_boxed_6259_ = lean_unbox_usize(v_i_6256_);
lean_dec(v_i_6256_);
v_res_6260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6258_, v_i_boxed_6259_, v_bs_6257_);
return v_res_6260_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6272_ = l_Lean_stringToMessageData(v___x_6271_);
return v___x_6272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_, lean_object* v_a_6276_, lean_object* v_a_6277_, lean_object* v_a_6278_, lean_object* v_a_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_){
_start:
{
lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6287_; lean_object* v___y_6288_; lean_object* v___y_6289_; lean_object* v___y_6290_; lean_object* v___y_6291_; lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___x_6306_; uint8_t v___x_6307_; 
v___x_6306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6273_);
v___x_6307_ = l_Lean_Syntax_isOfKind(v_stx_6273_, v___x_6306_);
if (v___x_6307_ == 0)
{
lean_object* v___x_6308_; 
lean_dec(v_stx_6273_);
v___x_6308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6308_;
}
else
{
lean_object* v___x_6309_; lean_object* v_tk_6310_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6314_; lean_object* v___y_6315_; lean_object* v___y_6316_; lean_object* v___y_6317_; lean_object* v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v___y_6350_; lean_object* v_a_6351_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v_val_x3f_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; lean_object* v___x_6395_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v_ty_x3f_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6407_; lean_object* v_pat_x3f_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v___x_6435_; uint8_t v___x_6436_; 
v___x_6309_ = lean_unsigned_to_nat(0u);
v_tk_6310_ = l_Lean_Syntax_getArg(v_stx_6273_, v___x_6309_);
v___x_6395_ = lean_unsigned_to_nat(1u);
v___x_6435_ = l_Lean_Syntax_getArg(v_stx_6273_, v___x_6395_);
v___x_6436_ = l_Lean_Syntax_isNone(v___x_6435_);
if (v___x_6436_ == 0)
{
uint8_t v___x_6437_; 
lean_inc(v___x_6435_);
v___x_6437_ = l_Lean_Syntax_matchesNull(v___x_6435_, v___x_6395_);
if (v___x_6437_ == 0)
{
lean_object* v___x_6438_; 
lean_dec(v___x_6435_);
lean_dec(v_tk_6310_);
lean_dec(v_stx_6273_);
v___x_6438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6438_;
}
else
{
lean_object* v_pat_x3f_6439_; lean_object* v___x_6440_; uint8_t v___x_6441_; 
v_pat_x3f_6439_ = l_Lean_Syntax_getArg(v___x_6435_, v___x_6309_);
lean_dec(v___x_6435_);
v___x_6440_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6439_);
v___x_6441_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6439_, v___x_6440_);
if (v___x_6441_ == 0)
{
lean_object* v___x_6442_; 
lean_dec(v_pat_x3f_6439_);
lean_dec(v_tk_6310_);
lean_dec(v_stx_6273_);
v___x_6442_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6442_;
}
else
{
lean_object* v___x_6443_; 
v___x_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6443_, 0, v_pat_x3f_6439_);
v_pat_x3f_6418_ = v___x_6443_;
v___y_6419_ = v_a_6274_;
v___y_6420_ = v_a_6275_;
v___y_6421_ = v_a_6276_;
v___y_6422_ = v_a_6277_;
v___y_6423_ = v_a_6278_;
v___y_6424_ = v_a_6279_;
v___y_6425_ = v_a_6280_;
v___y_6426_ = v_a_6281_;
goto v___jp_6417_;
}
}
}
else
{
lean_object* v___x_6444_; 
lean_dec(v___x_6435_);
v___x_6444_ = lean_box(0);
v_pat_x3f_6418_ = v___x_6444_;
v___y_6419_ = v_a_6274_;
v___y_6420_ = v_a_6275_;
v___y_6421_ = v_a_6276_;
v___y_6422_ = v_a_6277_;
v___y_6423_ = v_a_6278_;
v___y_6424_ = v_a_6279_;
v___y_6425_ = v_a_6280_;
v___y_6426_ = v_a_6281_;
goto v___jp_6417_;
}
v___jp_6311_:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; size_t v_sz_6325_; size_t v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6323_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6310_, v___y_6322_, v___y_6317_);
lean_dec(v___y_6317_);
v___x_6324_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6320_);
lean_dec_ref(v___y_6320_);
v_sz_6325_ = lean_array_size(v___x_6324_);
v___x_6326_ = ((size_t)0ULL);
v___x_6327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6325_, v___x_6326_, v___x_6324_);
v___x_6328_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6314_, v___y_6319_, v___y_6321_, v___y_6312_, v___y_6315_);
if (lean_obj_tag(v___x_6328_) == 0)
{
lean_object* v_a_6329_; lean_object* v___f_6330_; lean_object* v___x_6331_; 
v_a_6329_ = lean_ctor_get(v___x_6328_, 0);
lean_inc_n(v_a_6329_, 2);
lean_dec_ref_known(v___x_6328_, 1);
v___f_6330_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6330_, 0, v___x_6327_);
lean_closure_set(v___f_6330_, 1, v___x_6323_);
lean_closure_set(v___f_6330_, 2, v_a_6329_);
v___x_6331_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6329_, v___f_6330_, v___y_6318_, v___y_6314_, v___y_6316_, v___y_6313_, v___y_6319_, v___y_6321_, v___y_6312_, v___y_6315_);
return v___x_6331_;
}
else
{
lean_object* v_a_6332_; lean_object* v___x_6334_; uint8_t v_isShared_6335_; uint8_t v_isSharedCheck_6339_; 
lean_dec_ref(v___x_6327_);
lean_dec_ref(v___x_6323_);
v_a_6332_ = lean_ctor_get(v___x_6328_, 0);
v_isSharedCheck_6339_ = !lean_is_exclusive(v___x_6328_);
if (v_isSharedCheck_6339_ == 0)
{
v___x_6334_ = v___x_6328_;
v_isShared_6335_ = v_isSharedCheck_6339_;
goto v_resetjp_6333_;
}
else
{
lean_inc(v_a_6332_);
lean_dec(v___x_6328_);
v___x_6334_ = lean_box(0);
v_isShared_6335_ = v_isSharedCheck_6339_;
goto v_resetjp_6333_;
}
v_resetjp_6333_:
{
lean_object* v___x_6337_; 
if (v_isShared_6335_ == 0)
{
v___x_6337_ = v___x_6334_;
goto v_reusejp_6336_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_a_6332_);
v___x_6337_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6336_;
}
v_reusejp_6336_:
{
return v___x_6337_;
}
}
}
}
v___jp_6340_:
{
if (lean_obj_tag(v___y_6347_) == 1)
{
if (lean_obj_tag(v_a_6351_) == 0)
{
lean_object* v_val_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v_val_6352_ = lean_ctor_get(v___y_6347_, 0);
lean_inc(v_val_6352_);
lean_dec_ref_known(v___y_6347_, 1);
v___x_6353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6310_);
v___x_6354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6354_, 0, v_tk_6310_);
lean_ctor_set(v___x_6354_, 1, v___x_6353_);
v___y_6312_ = v___y_6341_;
v___y_6313_ = v___y_6343_;
v___y_6314_ = v___y_6342_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v___y_6348_;
v___y_6319_ = v___y_6349_;
v___y_6320_ = v_val_6352_;
v___y_6321_ = v___y_6350_;
v___y_6322_ = v___x_6354_;
goto v___jp_6311_;
}
else
{
lean_object* v_val_6355_; lean_object* v_val_6356_; 
v_val_6355_ = lean_ctor_get(v___y_6347_, 0);
lean_inc(v_val_6355_);
lean_dec_ref_known(v___y_6347_, 1);
v_val_6356_ = lean_ctor_get(v_a_6351_, 0);
lean_inc(v_val_6356_);
lean_dec_ref_known(v_a_6351_, 1);
v___y_6312_ = v___y_6341_;
v___y_6313_ = v___y_6343_;
v___y_6314_ = v___y_6342_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___y_6346_;
v___y_6317_ = v___y_6345_;
v___y_6318_ = v___y_6348_;
v___y_6319_ = v___y_6349_;
v___y_6320_ = v_val_6355_;
v___y_6321_ = v___y_6350_;
v___y_6322_ = v_val_6356_;
goto v___jp_6311_;
}
}
else
{
lean_dec(v___y_6347_);
if (lean_obj_tag(v___y_6345_) == 1)
{
if (lean_obj_tag(v_a_6351_) == 0)
{
lean_object* v_val_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; 
v_val_6357_ = lean_ctor_get(v___y_6345_, 0);
lean_inc(v_val_6357_);
lean_dec_ref_known(v___y_6345_, 1);
v___x_6358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6359_, 0, v_tk_6310_);
lean_ctor_set(v___x_6359_, 1, v___x_6358_);
v___y_6284_ = v_val_6357_;
v___y_6285_ = v___y_6341_;
v___y_6286_ = v___y_6343_;
v___y_6287_ = v___y_6342_;
v___y_6288_ = v___y_6344_;
v___y_6289_ = v___y_6346_;
v___y_6290_ = v___y_6348_;
v___y_6291_ = v___y_6349_;
v___y_6292_ = v___y_6350_;
v___y_6293_ = v___x_6359_;
goto v___jp_6283_;
}
else
{
lean_object* v_val_6360_; lean_object* v_val_6361_; 
lean_dec(v_tk_6310_);
v_val_6360_ = lean_ctor_get(v___y_6345_, 0);
lean_inc(v_val_6360_);
lean_dec_ref_known(v___y_6345_, 1);
v_val_6361_ = lean_ctor_get(v_a_6351_, 0);
lean_inc(v_val_6361_);
lean_dec_ref_known(v_a_6351_, 1);
v___y_6284_ = v_val_6360_;
v___y_6285_ = v___y_6341_;
v___y_6286_ = v___y_6343_;
v___y_6287_ = v___y_6342_;
v___y_6288_ = v___y_6344_;
v___y_6289_ = v___y_6346_;
v___y_6290_ = v___y_6348_;
v___y_6291_ = v___y_6349_;
v___y_6292_ = v___y_6350_;
v___y_6293_ = v_val_6361_;
goto v___jp_6283_;
}
}
else
{
lean_object* v___x_6362_; lean_object* v___x_6363_; 
lean_dec(v_a_6351_);
lean_dec(v___y_6345_);
lean_dec(v_tk_6310_);
v___x_6362_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6363_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6362_, v___y_6349_, v___y_6350_, v___y_6341_, v___y_6344_);
return v___x_6363_;
}
}
}
v___jp_6364_:
{
if (lean_obj_tag(v___y_6366_) == 0)
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_box(0);
v___y_6341_ = v___y_6374_;
v___y_6342_ = v___y_6369_;
v___y_6343_ = v___y_6371_;
v___y_6344_ = v___y_6375_;
v___y_6345_ = v___y_6365_;
v___y_6346_ = v___y_6370_;
v___y_6347_ = v_val_x3f_6367_;
v___y_6348_ = v___y_6368_;
v___y_6349_ = v___y_6372_;
v___y_6350_ = v___y_6373_;
v_a_6351_ = v___x_6376_;
goto v___jp_6340_;
}
else
{
lean_object* v_val_6377_; lean_object* v___x_6379_; uint8_t v_isShared_6380_; uint8_t v_isSharedCheck_6394_; 
v_val_6377_ = lean_ctor_get(v___y_6366_, 0);
v_isSharedCheck_6394_ = !lean_is_exclusive(v___y_6366_);
if (v_isSharedCheck_6394_ == 0)
{
v___x_6379_ = v___y_6366_;
v_isShared_6380_ = v_isSharedCheck_6394_;
goto v_resetjp_6378_;
}
else
{
lean_inc(v_val_6377_);
lean_dec(v___y_6366_);
v___x_6379_ = lean_box(0);
v_isShared_6380_ = v_isSharedCheck_6394_;
goto v_resetjp_6378_;
}
v_resetjp_6378_:
{
lean_object* v___x_6381_; 
v___x_6381_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6377_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_);
if (lean_obj_tag(v___x_6381_) == 0)
{
lean_object* v_a_6382_; lean_object* v___x_6384_; 
v_a_6382_ = lean_ctor_get(v___x_6381_, 0);
lean_inc(v_a_6382_);
lean_dec_ref_known(v___x_6381_, 1);
if (v_isShared_6380_ == 0)
{
lean_ctor_set(v___x_6379_, 0, v_a_6382_);
v___x_6384_ = v___x_6379_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6385_; 
v_reuseFailAlloc_6385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6385_, 0, v_a_6382_);
v___x_6384_ = v_reuseFailAlloc_6385_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
v___y_6341_ = v___y_6374_;
v___y_6342_ = v___y_6369_;
v___y_6343_ = v___y_6371_;
v___y_6344_ = v___y_6375_;
v___y_6345_ = v___y_6365_;
v___y_6346_ = v___y_6370_;
v___y_6347_ = v_val_x3f_6367_;
v___y_6348_ = v___y_6368_;
v___y_6349_ = v___y_6372_;
v___y_6350_ = v___y_6373_;
v_a_6351_ = v___x_6384_;
goto v___jp_6340_;
}
}
else
{
lean_object* v_a_6386_; lean_object* v___x_6388_; uint8_t v_isShared_6389_; uint8_t v_isSharedCheck_6393_; 
lean_del_object(v___x_6379_);
lean_dec(v_val_x3f_6367_);
lean_dec(v___y_6365_);
lean_dec(v_tk_6310_);
v_a_6386_ = lean_ctor_get(v___x_6381_, 0);
v_isSharedCheck_6393_ = !lean_is_exclusive(v___x_6381_);
if (v_isSharedCheck_6393_ == 0)
{
v___x_6388_ = v___x_6381_;
v_isShared_6389_ = v_isSharedCheck_6393_;
goto v_resetjp_6387_;
}
else
{
lean_inc(v_a_6386_);
lean_dec(v___x_6381_);
v___x_6388_ = lean_box(0);
v_isShared_6389_ = v_isSharedCheck_6393_;
goto v_resetjp_6387_;
}
v_resetjp_6387_:
{
lean_object* v___x_6391_; 
if (v_isShared_6389_ == 0)
{
v___x_6391_ = v___x_6388_;
goto v_reusejp_6390_;
}
else
{
lean_object* v_reuseFailAlloc_6392_; 
v_reuseFailAlloc_6392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_a_6386_);
v___x_6391_ = v_reuseFailAlloc_6392_;
goto v_reusejp_6390_;
}
v_reusejp_6390_:
{
return v___x_6391_;
}
}
}
}
}
}
v___jp_6396_:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; uint8_t v___x_6410_; 
v___x_6408_ = lean_unsigned_to_nat(3u);
v___x_6409_ = l_Lean_Syntax_getArg(v_stx_6273_, v___x_6408_);
lean_dec(v_stx_6273_);
v___x_6410_ = l_Lean_Syntax_isNone(v___x_6409_);
if (v___x_6410_ == 0)
{
uint8_t v___x_6411_; 
lean_inc(v___x_6409_);
v___x_6411_ = l_Lean_Syntax_matchesNull(v___x_6409_, v___y_6398_);
if (v___x_6411_ == 0)
{
lean_object* v___x_6412_; 
lean_dec(v___x_6409_);
lean_dec(v_ty_x3f_6399_);
lean_dec(v___y_6397_);
lean_dec(v_tk_6310_);
v___x_6412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6412_;
}
else
{
lean_object* v___x_6413_; lean_object* v_val_x3f_6414_; lean_object* v___x_6415_; 
v___x_6413_ = l_Lean_Syntax_getArg(v___x_6409_, v___x_6395_);
lean_dec(v___x_6409_);
v_val_x3f_6414_ = l_Lean_Syntax_getArgs(v___x_6413_);
lean_dec(v___x_6413_);
v___x_6415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6415_, 0, v_val_x3f_6414_);
v___y_6365_ = v_ty_x3f_6399_;
v___y_6366_ = v___y_6397_;
v_val_x3f_6367_ = v___x_6415_;
v___y_6368_ = v___y_6400_;
v___y_6369_ = v___y_6401_;
v___y_6370_ = v___y_6402_;
v___y_6371_ = v___y_6403_;
v___y_6372_ = v___y_6404_;
v___y_6373_ = v___y_6405_;
v___y_6374_ = v___y_6406_;
v___y_6375_ = v___y_6407_;
goto v___jp_6364_;
}
}
else
{
lean_object* v___x_6416_; 
lean_dec(v___x_6409_);
v___x_6416_ = lean_box(0);
v___y_6365_ = v_ty_x3f_6399_;
v___y_6366_ = v___y_6397_;
v_val_x3f_6367_ = v___x_6416_;
v___y_6368_ = v___y_6400_;
v___y_6369_ = v___y_6401_;
v___y_6370_ = v___y_6402_;
v___y_6371_ = v___y_6403_;
v___y_6372_ = v___y_6404_;
v___y_6373_ = v___y_6405_;
v___y_6374_ = v___y_6406_;
v___y_6375_ = v___y_6407_;
goto v___jp_6364_;
}
}
v___jp_6417_:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; uint8_t v___x_6429_; 
v___x_6427_ = lean_unsigned_to_nat(2u);
v___x_6428_ = l_Lean_Syntax_getArg(v_stx_6273_, v___x_6427_);
v___x_6429_ = l_Lean_Syntax_isNone(v___x_6428_);
if (v___x_6429_ == 0)
{
uint8_t v___x_6430_; 
lean_inc(v___x_6428_);
v___x_6430_ = l_Lean_Syntax_matchesNull(v___x_6428_, v___x_6427_);
if (v___x_6430_ == 0)
{
lean_object* v___x_6431_; 
lean_dec(v___x_6428_);
lean_dec(v_pat_x3f_6418_);
lean_dec(v_tk_6310_);
lean_dec(v_stx_6273_);
v___x_6431_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6431_;
}
else
{
lean_object* v_ty_x3f_6432_; lean_object* v___x_6433_; 
v_ty_x3f_6432_ = l_Lean_Syntax_getArg(v___x_6428_, v___x_6395_);
lean_dec(v___x_6428_);
v___x_6433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6433_, 0, v_ty_x3f_6432_);
v___y_6397_ = v_pat_x3f_6418_;
v___y_6398_ = v___x_6427_;
v_ty_x3f_6399_ = v___x_6433_;
v___y_6400_ = v___y_6419_;
v___y_6401_ = v___y_6420_;
v___y_6402_ = v___y_6421_;
v___y_6403_ = v___y_6422_;
v___y_6404_ = v___y_6423_;
v___y_6405_ = v___y_6424_;
v___y_6406_ = v___y_6425_;
v___y_6407_ = v___y_6426_;
goto v___jp_6396_;
}
}
else
{
lean_object* v___x_6434_; 
lean_dec(v___x_6428_);
v___x_6434_ = lean_box(0);
v___y_6397_ = v_pat_x3f_6418_;
v___y_6398_ = v___x_6427_;
v_ty_x3f_6399_ = v___x_6434_;
v___y_6400_ = v___y_6419_;
v___y_6401_ = v___y_6420_;
v___y_6402_ = v___y_6421_;
v___y_6403_ = v___y_6422_;
v___y_6404_ = v___y_6423_;
v___y_6405_ = v___y_6424_;
v___y_6406_ = v___y_6425_;
v___y_6407_ = v___y_6426_;
goto v___jp_6396_;
}
}
}
v___jp_6283_:
{
lean_object* v___x_6294_; 
v___x_6294_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6287_, v___y_6291_, v___y_6292_, v___y_6285_, v___y_6288_);
if (lean_obj_tag(v___x_6294_) == 0)
{
lean_object* v_a_6295_; lean_object* v___f_6296_; lean_object* v___x_6297_; 
v_a_6295_ = lean_ctor_get(v___x_6294_, 0);
lean_inc_n(v_a_6295_, 2);
lean_dec_ref_known(v___x_6294_, 1);
v___f_6296_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6296_, 0, v___y_6293_);
lean_closure_set(v___f_6296_, 1, v___y_6284_);
lean_closure_set(v___f_6296_, 2, v_a_6295_);
v___x_6297_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6295_, v___f_6296_, v___y_6290_, v___y_6287_, v___y_6289_, v___y_6286_, v___y_6291_, v___y_6292_, v___y_6285_, v___y_6288_);
return v___x_6297_;
}
else
{
lean_object* v_a_6298_; lean_object* v___x_6300_; uint8_t v_isShared_6301_; uint8_t v_isSharedCheck_6305_; 
lean_dec_ref(v___y_6293_);
lean_dec(v___y_6284_);
v_a_6298_ = lean_ctor_get(v___x_6294_, 0);
v_isSharedCheck_6305_ = !lean_is_exclusive(v___x_6294_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6300_ = v___x_6294_;
v_isShared_6301_ = v_isSharedCheck_6305_;
goto v_resetjp_6299_;
}
else
{
lean_inc(v_a_6298_);
lean_dec(v___x_6294_);
v___x_6300_ = lean_box(0);
v_isShared_6301_ = v_isSharedCheck_6305_;
goto v_resetjp_6299_;
}
v_resetjp_6299_:
{
lean_object* v___x_6303_; 
if (v_isShared_6301_ == 0)
{
v___x_6303_ = v___x_6300_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_a_6298_);
v___x_6303_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
return v___x_6303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_, lean_object* v_a_6452_, lean_object* v_a_6453_, lean_object* v_a_6454_){
_start:
{
lean_object* v_res_6455_; 
v_res_6455_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6445_, v_a_6446_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_, v_a_6451_, v_a_6452_, v_a_6453_);
lean_dec(v_a_6453_);
lean_dec_ref(v_a_6452_);
lean_dec(v_a_6451_);
lean_dec_ref(v_a_6450_);
lean_dec(v_a_6449_);
lean_dec_ref(v_a_6448_);
lean_dec(v_a_6447_);
lean_dec_ref(v_a_6446_);
return v_res_6455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6456_, lean_object* v_msg_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_){
_start:
{
lean_object* v___x_6467_; 
v___x_6467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6457_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
return v___x_6467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6468_, lean_object* v_msg_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_){
_start:
{
lean_object* v_res_6479_; 
v_res_6479_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6468_, v_msg_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_);
lean_dec(v___y_6477_);
lean_dec_ref(v___y_6476_);
lean_dec(v___y_6475_);
lean_dec_ref(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec_ref(v___y_6472_);
lean_dec(v___y_6471_);
lean_dec_ref(v___y_6470_);
return v_res_6479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v___x_6485_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6488_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6489_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6485_, v___x_6486_, v___x_6487_, v___x_6488_);
return v___x_6489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6490_){
_start:
{
lean_object* v_res_6491_; 
v_res_6491_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6492_, lean_object* v_ty_x3f_6493_, lean_object* v_a_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_){
_start:
{
lean_object* v___x_6504_; 
v___x_6504_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6492_, v_ty_x3f_6493_, v_a_6494_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
if (lean_obj_tag(v___x_6504_) == 0)
{
lean_object* v_a_6505_; lean_object* v___x_6506_; 
v_a_6505_ = lean_ctor_get(v___x_6504_, 0);
lean_inc(v_a_6505_);
lean_dec_ref_known(v___x_6504_, 1);
v___x_6506_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6505_, v___y_6496_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
return v___x_6506_;
}
else
{
lean_object* v_a_6507_; lean_object* v___x_6509_; uint8_t v_isShared_6510_; uint8_t v_isSharedCheck_6514_; 
v_a_6507_ = lean_ctor_get(v___x_6504_, 0);
v_isSharedCheck_6514_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6514_ == 0)
{
v___x_6509_ = v___x_6504_;
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
else
{
lean_inc(v_a_6507_);
lean_dec(v___x_6504_);
v___x_6509_ = lean_box(0);
v_isShared_6510_ = v_isSharedCheck_6514_;
goto v_resetjp_6508_;
}
v_resetjp_6508_:
{
lean_object* v___x_6512_; 
if (v_isShared_6510_ == 0)
{
v___x_6512_ = v___x_6509_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6513_; 
v_reuseFailAlloc_6513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6513_, 0, v_a_6507_);
v___x_6512_ = v_reuseFailAlloc_6513_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
return v___x_6512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6515_, lean_object* v_ty_x3f_6516_, lean_object* v_a_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_){
_start:
{
lean_object* v_res_6527_; 
v_res_6527_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6515_, v_ty_x3f_6516_, v_a_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_);
lean_dec(v___y_6525_);
lean_dec_ref(v___y_6524_);
lean_dec(v___y_6523_);
lean_dec_ref(v___y_6522_);
lean_dec(v___y_6521_);
lean_dec_ref(v___y_6520_);
lean_dec(v___y_6519_);
lean_dec_ref(v___y_6518_);
return v_res_6527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_, lean_object* v_a_6539_, lean_object* v_a_6540_, lean_object* v_a_6541_, lean_object* v_a_6542_){
_start:
{
lean_object* v___x_6544_; uint8_t v___x_6545_; 
v___x_6544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6534_);
v___x_6545_ = l_Lean_Syntax_isOfKind(v_stx_6534_, v___x_6544_);
if (v___x_6545_ == 0)
{
lean_object* v___x_6546_; 
lean_dec(v_stx_6534_);
v___x_6546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6546_;
}
else
{
lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v_ty_x3f_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___x_6572_; lean_object* v___x_6573_; uint8_t v___x_6574_; 
v___x_6547_ = lean_unsigned_to_nat(1u);
v___x_6548_ = l_Lean_Syntax_getArg(v_stx_6534_, v___x_6547_);
v___x_6572_ = lean_unsigned_to_nat(2u);
v___x_6573_ = l_Lean_Syntax_getArg(v_stx_6534_, v___x_6572_);
lean_dec(v_stx_6534_);
v___x_6574_ = l_Lean_Syntax_isNone(v___x_6573_);
if (v___x_6574_ == 0)
{
uint8_t v___x_6575_; 
lean_inc(v___x_6573_);
v___x_6575_ = l_Lean_Syntax_matchesNull(v___x_6573_, v___x_6572_);
if (v___x_6575_ == 0)
{
lean_object* v___x_6576_; 
lean_dec(v___x_6573_);
lean_dec(v___x_6548_);
v___x_6576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6576_;
}
else
{
lean_object* v_ty_x3f_6577_; lean_object* v___x_6578_; 
v_ty_x3f_6577_ = l_Lean_Syntax_getArg(v___x_6573_, v___x_6547_);
lean_dec(v___x_6573_);
v___x_6578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6578_, 0, v_ty_x3f_6577_);
v_ty_x3f_6550_ = v___x_6578_;
v___y_6551_ = v_a_6535_;
v___y_6552_ = v_a_6536_;
v___y_6553_ = v_a_6537_;
v___y_6554_ = v_a_6538_;
v___y_6555_ = v_a_6539_;
v___y_6556_ = v_a_6540_;
v___y_6557_ = v_a_6541_;
v___y_6558_ = v_a_6542_;
goto v___jp_6549_;
}
}
else
{
lean_object* v___x_6579_; 
lean_dec(v___x_6573_);
v___x_6579_ = lean_box(0);
v_ty_x3f_6550_ = v___x_6579_;
v___y_6551_ = v_a_6535_;
v___y_6552_ = v_a_6536_;
v___y_6553_ = v_a_6537_;
v___y_6554_ = v_a_6538_;
v___y_6555_ = v_a_6539_;
v___y_6556_ = v_a_6540_;
v___y_6557_ = v_a_6541_;
v___y_6558_ = v_a_6542_;
goto v___jp_6549_;
}
v___jp_6549_:
{
lean_object* v_pats_6559_; lean_object* v___x_6560_; 
v_pats_6559_ = l_Lean_Syntax_getArgs(v___x_6548_);
lean_dec(v___x_6548_);
v___x_6560_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6552_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6560_) == 0)
{
lean_object* v_a_6561_; lean_object* v___f_6562_; lean_object* v___x_6563_; 
v_a_6561_ = lean_ctor_get(v___x_6560_, 0);
lean_inc_n(v_a_6561_, 2);
lean_dec_ref_known(v___x_6560_, 1);
v___f_6562_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6562_, 0, v_pats_6559_);
lean_closure_set(v___f_6562_, 1, v_ty_x3f_6550_);
lean_closure_set(v___f_6562_, 2, v_a_6561_);
v___x_6563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6561_, v___f_6562_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
return v___x_6563_;
}
else
{
lean_object* v_a_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6571_; 
lean_dec_ref(v_pats_6559_);
lean_dec(v_ty_x3f_6550_);
v_a_6564_ = lean_ctor_get(v___x_6560_, 0);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6560_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6566_ = v___x_6560_;
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_a_6564_);
lean_dec(v___x_6560_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v___x_6569_; 
if (v_isShared_6567_ == 0)
{
v___x_6569_ = v___x_6566_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6564_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
return v___x_6569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_){
_start:
{
lean_object* v_res_6590_; 
v_res_6590_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6580_, v_a_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_, v_a_6587_, v_a_6588_);
lean_dec(v_a_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_a_6586_);
lean_dec_ref(v_a_6585_);
lean_dec(v_a_6584_);
lean_dec_ref(v_a_6583_);
lean_dec(v_a_6582_);
lean_dec_ref(v_a_6581_);
return v_res_6590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; 
v___x_6596_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6599_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6600_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6596_, v___x_6597_, v___x_6598_, v___x_6599_);
return v___x_6600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6601_){
_start:
{
lean_object* v_res_6602_; 
v_res_6602_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6602_;
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
