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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
v___x_867_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v_ref_845_, v_info_846_, v_explicit_847_, v___y_865_, v___y_866_);
lean_dec(v___y_865_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_snd_869_);
lean_dec_ref(v___x_867_);
v___x_870_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___y_864_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_856_ = v___y_864_;
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
v___y_856_ = v___y_864_;
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
v___y_864_ = v___y_875_;
v___y_865_ = v___y_874_;
v___y_866_ = v_ps_849_;
goto v___jp_863_;
}
else
{
lean_object* v_tail_876_; 
v_tail_876_ = lean_ctor_get(v_ps_849_, 1);
lean_inc(v_tail_876_);
lean_dec_ref_known(v_ps_849_, 2);
v___y_864_ = v___y_875_;
v___y_865_ = v___y_874_;
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
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
lean_ctor_set(v___x_969_, 3, v___x_968_);
lean_ctor_set(v___x_969_, 4, v___x_967_);
lean_ctor_set(v___x_969_, 5, v___x_967_);
lean_ctor_set(v___x_969_, 6, v___x_967_);
lean_ctor_set(v___x_969_, 7, v___x_967_);
lean_ctor_set(v___x_969_, 8, v___x_967_);
lean_ctor_set(v___x_969_, 9, v___x_967_);
lean_ctor_set(v___x_969_, 10, v___x_966_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_unsigned_to_nat(32u);
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = ((size_t)5ULL);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_unsigned_to_nat(32u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_978_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
lean_ctor_set(v___x_978_, 2, v___x_974_);
lean_ctor_set(v___x_978_, 3, v___x_974_);
lean_ctor_set_usize(v___x_978_, 4, v___x_973_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_979_ = lean_box(1);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
lean_ctor_set(v___x_982_, 2, v___x_979_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1004_, lean_object* v_declHint_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_env_1010_; uint8_t v___x_1011_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_st_ref_get(v___y_1006_);
v_env_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc_ref(v_env_1010_);
lean_dec(v___x_1009_);
v___x_1011_ = l_Lean_Name_isAnonymous(v_declHint_1005_);
if (v___x_1011_ == 0)
{
uint8_t v_isExporting_1012_; 
v_isExporting_1012_ = lean_ctor_get_uint8(v_env_1010_, sizeof(void*)*13);
if (v_isExporting_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v_env_1010_);
lean_dec(v_declHint_1005_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_msg_1004_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
lean_inc_ref(v_env_1010_);
v___x_1014_ = l_Lean_Environment_setExporting(v_env_1010_, v___x_1011_);
lean_inc(v_declHint_1005_);
lean_inc_ref(v___x_1014_);
v___x_1015_ = l_Lean_Environment_contains(v___x_1014_, v_declHint_1005_, v_isExporting_1012_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec_ref(v___x_1014_);
lean_dec_ref(v_env_1010_);
lean_dec(v_declHint_1005_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_msg_1004_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_c_1022_; lean_object* v___x_1023_; 
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1019_ = l_Lean_Options_empty;
v___x_1020_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1014_);
lean_ctor_set(v___x_1020_, 1, v___x_1017_);
lean_ctor_set(v___x_1020_, 2, v___x_1018_);
lean_ctor_set(v___x_1020_, 3, v___x_1019_);
lean_inc(v_declHint_1005_);
v___x_1021_ = l_Lean_MessageData_ofConstName(v_declHint_1005_, v___x_1011_);
v_c_1022_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1022_, 0, v___x_1020_);
lean_ctor_set(v_c_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1010_, v_declHint_1005_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_env_1010_);
lean_dec(v_declHint_1005_);
v___x_1024_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_c_1022_);
v___x_1026_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_MessageData_note(v___x_1027_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_msg_1004_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
else
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1065_; 
v_val_1031_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1033_ = v___x_1023_;
v_isShared_1034_ = v_isSharedCheck_1065_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v___x_1023_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1065_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v_moduleNames_1036_; lean_object* v_mod_1037_; uint8_t v___x_1038_; 
v___x_1035_ = l_Lean_Environment_header(v_env_1010_);
lean_dec_ref(v_env_1010_);
v_moduleNames_1036_ = lean_ctor_get(v___x_1035_, 4);
lean_inc_ref(v_moduleNames_1036_);
lean_dec_ref(v___x_1035_);
v_mod_1037_ = lean_array_get(v___x_1008_, v_moduleNames_1036_, v_val_1031_);
lean_dec(v_val_1031_);
lean_dec_ref(v_moduleNames_1036_);
v___x_1038_ = l_Lean_isPrivateName(v_declHint_1005_);
lean_dec(v_declHint_1005_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_c_1022_);
v___x_1041_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_MessageData_ofName(v_mod_1037_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_MessageData_note(v___x_1046_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_msg_1004_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1048_);
v___x_1050_ = v___x_1033_;
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
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_c_1022_);
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_ofName(v_mod_1037_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_MessageData_note(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_msg_1004_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1061_);
v___x_1063_ = v___x_1033_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1066_; 
lean_dec_ref(v_env_1010_);
lean_dec(v_declHint_1005_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1004_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1067_, lean_object* v_declHint_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1067_, v_declHint_1068_, v___y_1069_);
lean_dec(v___y_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
v___x_1079_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1072_, v_declHint_1073_, v___y_1077_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = l_Lean_unknownIdentifierMessageTag;
v___x_1085_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_msg_1090_, lean_object* v_declHint_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1090_, v_declHint_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object* v_msgData_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_env_1105_; uint8_t v___x_1106_; lean_object* v_env_1107_; lean_object* v___x_1108_; lean_object* v_toCold_1109_; lean_object* v_mctx_1110_; lean_object* v_lctx_1111_; lean_object* v_options_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1104_ = lean_st_ref_get(v___y_1102_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = 0;
v_env_1107_ = l_Lean_Environment_setRecordingDeps(v_env_1105_, v___x_1106_);
v___x_1108_ = lean_st_ref_get(v___y_1100_);
v_toCold_1109_ = lean_ctor_get(v___y_1101_, 0);
v_mctx_1110_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_mctx_1110_);
lean_dec(v___x_1108_);
v_lctx_1111_ = lean_ctor_get(v___y_1099_, 2);
v_options_1112_ = lean_ctor_get(v_toCold_1109_, 2);
lean_inc_ref(v_options_1112_);
lean_inc_ref(v_lctx_1111_);
v___x_1113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1113_, 0, v_env_1107_);
lean_ctor_set(v___x_1113_, 1, v_mctx_1110_);
lean_ctor_set(v___x_1113_, 2, v_lctx_1111_);
lean_ctor_set(v___x_1113_, 3, v_options_1112_);
v___x_1114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_msgData_1098_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msgData_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_ref_1129_; lean_object* v___x_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_ref_1129_ = lean_ctor_get(v___y_1126_, 2);
v___x_1130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_inc(v_ref_1129_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_ref_1129_);
lean_ctor_set(v___x_1135_, 1, v_a_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1147_, lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_toCold_1154_; lean_object* v_currRecDepth_1155_; lean_object* v_ref_1156_; uint16_t v_optionFlags_1157_; uint8_t v_suppressElabErrors_1158_; uint8_t v_isRecordingDeps_1159_; lean_object* v_ref_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_toCold_1154_ = lean_ctor_get(v___y_1151_, 0);
v_currRecDepth_1155_ = lean_ctor_get(v___y_1151_, 1);
v_ref_1156_ = lean_ctor_get(v___y_1151_, 2);
v_optionFlags_1157_ = lean_ctor_get_uint16(v___y_1151_, sizeof(void*)*3);
v_suppressElabErrors_1158_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1159_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*3 + 3);
v_ref_1160_ = l_Lean_replaceRef(v_ref_1147_, v_ref_1156_);
lean_inc(v_currRecDepth_1155_);
lean_inc_ref(v_toCold_1154_);
v___x_1161_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1161_, 0, v_toCold_1154_);
lean_ctor_set(v___x_1161_, 1, v_currRecDepth_1155_);
lean_ctor_set(v___x_1161_, 2, v_ref_1160_);
lean_ctor_set_uint16(v___x_1161_, sizeof(void*)*3, v_optionFlags_1157_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 2, v_suppressElabErrors_1158_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3 + 3, v_isRecordingDeps_1159_);
v___x_1162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1148_, v___y_1149_, v___y_1150_, v___x_1161_, v___y_1152_);
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
lean_object* v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1375_; uint8_t v_fst_1376_; lean_object* v_snd_1377_; lean_object* v_snd_1378_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1405_; 
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
v___x_1340_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1339_, v_paramInfo_1331_, v___y_1337_, v_params_1309_, v___y_1338_);
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
v___y_1337_ = v_fst_1376_;
v___y_1338_ = v_snd_1377_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v_ks_1830_; lean_object* v_vs_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1855_; 
v_ks_1830_ = lean_ctor_get(v_x_1826_, 0);
v_vs_1831_ = lean_ctor_get(v_x_1826_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_x_1826_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1833_ = v_x_1826_;
v_isShared_1834_ = v_isSharedCheck_1855_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_vs_1831_);
lean_inc(v_ks_1830_);
lean_dec(v_x_1826_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1855_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_array_get_size(v_ks_1830_);
v___x_1836_ = lean_nat_dec_lt(v_x_1827_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_dec(v_x_1827_);
v___x_1837_ = lean_array_push(v_ks_1830_, v_x_1828_);
v___x_1838_ = lean_array_push(v_vs_1831_, v_x_1829_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1838_);
lean_ctor_set(v___x_1833_, 0, v___x_1837_);
v___x_1840_ = v___x_1833_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_object* v_k_x27_1842_; uint8_t v___x_1843_; 
v_k_x27_1842_ = lean_array_fget_borrowed(v_ks_1830_, v_x_1827_);
v___x_1843_ = l_Lean_instBEqMVarId_beq(v_x_1828_, v_k_x27_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1845_; 
if (v_isShared_1834_ == 0)
{
v___x_1845_ = v___x_1833_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_ks_1830_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_vs_1831_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_add(v_x_1827_, v___x_1846_);
lean_dec(v_x_1827_);
v_x_1826_ = v___x_1845_;
v_x_1827_ = v___x_1847_;
goto _start;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = lean_array_fset(v_ks_1830_, v_x_1827_, v_x_1828_);
v___x_1851_ = lean_array_fset(v_vs_1831_, v_x_1827_, v_x_1829_);
lean_dec(v_x_1827_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1851_);
lean_ctor_set(v___x_1833_, 0, v___x_1850_);
v___x_1853_ = v___x_1833_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object* v_n_1856_, lean_object* v_k_1857_, lean_object* v_v_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_n_1856_, v___x_1859_, v_k_1857_, v_v_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object* v_x_1862_, size_t v_x_1863_, size_t v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1862_) == 0)
{
lean_object* v_es_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v_j_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_es_1867_ = lean_ctor_get(v_x_1862_, 0);
v___x_1868_ = ((size_t)31ULL);
v___x_1869_ = lean_usize_land(v_x_1863_, v___x_1868_);
v_j_1870_ = lean_usize_to_nat(v___x_1869_);
v___x_1871_ = lean_array_get_size(v_es_1867_);
v___x_1872_ = lean_nat_dec_lt(v_j_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec(v_j_1870_);
lean_dec(v_x_1866_);
lean_dec(v_x_1865_);
return v_x_1862_;
}
else
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1911_; 
lean_inc_ref(v_es_1867_);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1862_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_x_1862_, 0);
lean_dec(v_unused_1912_);
v___x_1874_ = v_x_1862_;
v_isShared_1875_ = v_isSharedCheck_1911_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_x_1862_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1911_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_v_1876_; lean_object* v___x_1877_; lean_object* v_xs_x27_1878_; lean_object* v___y_1880_; 
v_v_1876_ = lean_array_fget(v_es_1867_, v_j_1870_);
v___x_1877_ = lean_box(0);
v_xs_x27_1878_ = lean_array_fset(v_es_1867_, v_j_1870_, v___x_1877_);
switch(lean_obj_tag(v_v_1876_))
{
case 0:
{
lean_object* v_key_1885_; lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1896_; 
v_key_1885_ = lean_ctor_get(v_v_1876_, 0);
v_val_1886_ = lean_ctor_get(v_v_1876_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_v_1876_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1888_ = v_v_1876_;
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_inc(v_key_1885_);
lean_dec(v_v_1876_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint8_t v___x_1890_; 
v___x_1890_ = l_Lean_instBEqMVarId_beq(v_x_1865_, v_key_1885_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_del_object(v___x_1888_);
v___x_1891_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1885_, v_val_1886_, v_x_1865_, v_x_1866_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
v___y_1880_ = v___x_1892_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1894_; 
lean_dec(v_val_1886_);
lean_dec(v_key_1885_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_x_1866_);
lean_ctor_set(v___x_1888_, 0, v_x_1865_);
v___x_1894_ = v___x_1888_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_x_1865_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_x_1866_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v___y_1880_ = v___x_1894_;
goto v___jp_1879_;
}
}
}
}
case 1:
{
lean_object* v_node_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1909_; 
v_node_1897_ = lean_ctor_get(v_v_1876_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_v_1876_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1899_ = v_v_1876_;
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_node_1897_);
lean_dec(v_v_1876_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
size_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1901_ = ((size_t)5ULL);
v___x_1902_ = lean_usize_shift_right(v_x_1863_, v___x_1901_);
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_x_1864_, v___x_1903_);
v___x_1905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_node_1897_, v___x_1902_, v___x_1904_, v_x_1865_, v_x_1866_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1905_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1880_ = v___x_1907_;
goto v___jp_1879_;
}
}
}
default: 
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_x_1865_);
lean_ctor_set(v___x_1910_, 1, v_x_1866_);
v___y_1880_ = v___x_1910_;
goto v___jp_1879_;
}
}
v___jp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = lean_array_fset(v_xs_x27_1878_, v_j_1870_, v___y_1880_);
lean_dec(v_j_1870_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v_ks_1913_; lean_object* v_vs_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1932_; 
v_ks_1913_ = lean_ctor_get(v_x_1862_, 0);
v_vs_1914_ = lean_ctor_get(v_x_1862_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1862_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1916_ = v_x_1862_;
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_vs_1914_);
lean_inc(v_ks_1913_);
lean_dec(v_x_1862_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_ks_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_vs_1914_);
v___x_1919_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v_newNode_1920_; size_t v___x_1921_; uint8_t v___x_1922_; 
v_newNode_1920_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1919_, v_x_1865_, v_x_1866_);
v___x_1921_ = ((size_t)7ULL);
v___x_1922_ = lean_usize_dec_le(v___x_1921_, v_x_1864_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1923_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1920_);
v___x_1924_ = lean_unsigned_to_nat(4u);
v___x_1925_ = lean_nat_dec_lt(v___x_1923_, v___x_1924_);
lean_dec(v___x_1923_);
if (v___x_1925_ == 0)
{
lean_object* v_ks_1926_; lean_object* v_vs_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_ks_1926_ = lean_ctor_get(v_newNode_1920_, 0);
lean_inc_ref(v_ks_1926_);
v_vs_1927_ = lean_ctor_get(v_newNode_1920_, 1);
lean_inc_ref(v_vs_1927_);
lean_dec_ref(v_newNode_1920_);
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1864_, v_ks_1926_, v_vs_1927_, v___x_1928_, v___x_1929_);
lean_dec_ref(v_vs_1927_);
lean_dec_ref(v_ks_1926_);
return v___x_1930_;
}
else
{
return v_newNode_1920_;
}
}
else
{
return v_newNode_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1933_, lean_object* v_keys_1934_, lean_object* v_vals_1935_, lean_object* v_i_1936_, lean_object* v_entries_1937_){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_get_size(v_keys_1934_);
v___x_1939_ = lean_nat_dec_lt(v_i_1936_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec(v_i_1936_);
return v_entries_1937_;
}
else
{
lean_object* v_k_1940_; lean_object* v_v_1941_; uint64_t v___x_1942_; size_t v_h_1943_; size_t v___x_1944_; lean_object* v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v_h_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_k_1940_ = lean_array_fget_borrowed(v_keys_1934_, v_i_1936_);
v_v_1941_ = lean_array_fget_borrowed(v_vals_1935_, v_i_1936_);
v___x_1942_ = l_Lean_instHashableMVarId_hash(v_k_1940_);
v_h_1943_ = lean_uint64_to_usize(v___x_1942_);
v___x_1944_ = ((size_t)5ULL);
v___x_1945_ = lean_unsigned_to_nat(1u);
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_sub(v_depth_1933_, v___x_1946_);
v___x_1948_ = lean_usize_mul(v___x_1944_, v___x_1947_);
v_h_1949_ = lean_usize_shift_right(v_h_1943_, v___x_1948_);
v___x_1950_ = lean_nat_add(v_i_1936_, v___x_1945_);
lean_dec(v_i_1936_);
lean_inc(v_v_1941_);
lean_inc(v_k_1940_);
v___x_1951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1937_, v_h_1949_, v_depth_1933_, v_k_1940_, v_v_1941_);
v_i_1936_ = v___x_1950_;
v_entries_1937_ = v___x_1951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1953_, lean_object* v_keys_1954_, lean_object* v_vals_1955_, lean_object* v_i_1956_, lean_object* v_entries_1957_){
_start:
{
size_t v_depth_boxed_1958_; lean_object* v_res_1959_; 
v_depth_boxed_1958_ = lean_unbox_usize(v_depth_1953_);
lean_dec(v_depth_1953_);
v_res_1959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1958_, v_keys_1954_, v_vals_1955_, v_i_1956_, v_entries_1957_);
lean_dec_ref(v_vals_1955_);
lean_dec_ref(v_keys_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
size_t v_x_18562__boxed_1965_; size_t v_x_18563__boxed_1966_; lean_object* v_res_1967_; 
v_x_18562__boxed_1965_ = lean_unbox_usize(v_x_1961_);
lean_dec(v_x_1961_);
v_x_18563__boxed_1966_ = lean_unbox_usize(v_x_1962_);
lean_dec(v_x_1962_);
v_res_1967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1960_, v_x_18562__boxed_1965_, v_x_18563__boxed_1966_, v_x_1963_, v_x_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_){
_start:
{
uint64_t v___x_1971_; size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = l_Lean_instHashableMVarId_hash(v_x_1969_);
v___x_1972_ = lean_uint64_to_usize(v___x_1971_);
v___x_1973_ = ((size_t)1ULL);
v___x_1974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1968_, v___x_1972_, v___x_1973_, v_x_1969_, v_x_1970_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1975_, lean_object* v_val_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; lean_object* v_mctx_1980_; lean_object* v_cache_1981_; lean_object* v_zetaDeltaFVarIds_1982_; lean_object* v_postponed_1983_; lean_object* v_diag_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2013_; 
v___x_1979_ = lean_st_ref_take(v___y_1977_);
v_mctx_1980_ = lean_ctor_get(v___x_1979_, 0);
v_cache_1981_ = lean_ctor_get(v___x_1979_, 1);
v_zetaDeltaFVarIds_1982_ = lean_ctor_get(v___x_1979_, 2);
v_postponed_1983_ = lean_ctor_get(v___x_1979_, 3);
v_diag_1984_ = lean_ctor_get(v___x_1979_, 4);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1986_ = v___x_1979_;
v_isShared_1987_ = v_isSharedCheck_2013_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_diag_1984_);
lean_inc(v_postponed_1983_);
lean_inc(v_zetaDeltaFVarIds_1982_);
lean_inc(v_cache_1981_);
lean_inc(v_mctx_1980_);
lean_dec(v___x_1979_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2013_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_depth_1988_; lean_object* v_levelAssignDepth_1989_; lean_object* v_lmvarCounter_1990_; lean_object* v_mvarCounter_1991_; lean_object* v_lDecls_1992_; lean_object* v_decls_1993_; lean_object* v_userNames_1994_; lean_object* v_lAssignment_1995_; lean_object* v_eAssignment_1996_; lean_object* v_dAssignment_1997_; lean_object* v_synthNormMemo_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2012_; 
v_depth_1988_ = lean_ctor_get(v_mctx_1980_, 0);
v_levelAssignDepth_1989_ = lean_ctor_get(v_mctx_1980_, 1);
v_lmvarCounter_1990_ = lean_ctor_get(v_mctx_1980_, 2);
v_mvarCounter_1991_ = lean_ctor_get(v_mctx_1980_, 3);
v_lDecls_1992_ = lean_ctor_get(v_mctx_1980_, 4);
v_decls_1993_ = lean_ctor_get(v_mctx_1980_, 5);
v_userNames_1994_ = lean_ctor_get(v_mctx_1980_, 6);
v_lAssignment_1995_ = lean_ctor_get(v_mctx_1980_, 7);
v_eAssignment_1996_ = lean_ctor_get(v_mctx_1980_, 8);
v_dAssignment_1997_ = lean_ctor_get(v_mctx_1980_, 9);
v_synthNormMemo_1998_ = lean_ctor_get(v_mctx_1980_, 10);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_mctx_1980_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2000_ = v_mctx_1980_;
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_synthNormMemo_1998_);
lean_inc(v_dAssignment_1997_);
lean_inc(v_eAssignment_1996_);
lean_inc(v_lAssignment_1995_);
lean_inc(v_userNames_1994_);
lean_inc(v_decls_1993_);
lean_inc(v_lDecls_1992_);
lean_inc(v_mvarCounter_1991_);
lean_inc(v_lmvarCounter_1990_);
lean_inc(v_levelAssignDepth_1989_);
lean_inc(v_depth_1988_);
lean_dec(v_mctx_1980_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2012_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1996_, v_mvarId_1975_, v_val_1976_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 8, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_depth_1988_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_levelAssignDepth_1989_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_lmvarCounter_1990_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_mvarCounter_1991_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_lDecls_1992_);
lean_ctor_set(v_reuseFailAlloc_2011_, 5, v_decls_1993_);
lean_ctor_set(v_reuseFailAlloc_2011_, 6, v_userNames_1994_);
lean_ctor_set(v_reuseFailAlloc_2011_, 7, v_lAssignment_1995_);
lean_ctor_set(v_reuseFailAlloc_2011_, 8, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2011_, 9, v_dAssignment_1997_);
lean_ctor_set(v_reuseFailAlloc_2011_, 10, v_synthNormMemo_1998_);
v___x_2005_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2005_);
v___x_2007_ = v___x_1986_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_cache_1981_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_zetaDeltaFVarIds_1982_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_postponed_1983_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_diag_1984_);
v___x_2007_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_st_ref_put(v___y_1977_, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2002_);
return v___x_2009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_2014_, lean_object* v_val_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_2014_, v_val_2015_, v___y_2016_);
lean_dec(v___y_2016_);
return v_res_2018_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_14785__overap_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_14785__overap_2029_ = lean_panic_fn_borrowed(v___x_2028_, v_msg_2020_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
v___x_2030_ = lean_apply_7(v___x_14785__overap_2029_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, lean_box(0));
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_2040_, size_t v_i_2041_, size_t v_stop_2042_, lean_object* v_b_2043_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_eq(v_i_2041_, v_stop_2042_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; size_t v___x_2050_; size_t v___x_2051_; 
v___x_2045_ = lean_array_uget_borrowed(v_as_2040_, v_i_2041_);
v_fst_2046_ = lean_ctor_get(v___x_2045_, 0);
v_snd_2047_ = lean_ctor_get(v___x_2045_, 1);
lean_inc(v_snd_2047_);
v___x_2048_ = l_Lean_mkFVar(v_snd_2047_);
lean_inc(v_fst_2046_);
v___x_2049_ = l_Lean_Meta_FVarSubst_insert(v_b_2043_, v_fst_2046_, v___x_2048_);
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2041_, v___x_2050_);
v_i_2041_ = v___x_2051_;
v_b_2043_ = v___x_2049_;
goto _start;
}
else
{
return v_b_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_2053_, lean_object* v_i_2054_, lean_object* v_stop_2055_, lean_object* v_b_2056_){
_start:
{
size_t v_i_boxed_2057_; size_t v_stop_boxed_2058_; lean_object* v_res_2059_; 
v_i_boxed_2057_ = lean_unbox_usize(v_i_2054_);
lean_dec(v_i_2054_);
v_stop_boxed_2058_ = lean_unbox_usize(v_stop_2055_);
lean_dec(v_stop_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_2053_, v_i_boxed_2057_, v_stop_boxed_2058_, v_b_2056_);
lean_dec_ref(v_as_2053_);
return v_res_2059_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2060_; lean_object* v_dummy_2061_; 
v___x_2060_ = lean_box(0);
v_dummy_2061_ = l_Lean_Expr_sort___override(v___x_2060_);
return v_dummy_2061_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2066_ = lean_unsigned_to_nat(62u);
v___x_2067_ = lean_unsigned_to_nat(323u);
v___x_2068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2070_ = l_mkPanicMessageWithDecl(v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v_snd_2073_, lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v___x_2076_, lean_object* v_e_2077_, lean_object* v___x_2078_, lean_object* v_head_2079_, lean_object* v_fst_2080_, lean_object* v_tail_2081_, uint8_t v___x_2082_, lean_object* v_snd_2083_, lean_object* v___x_2084_, lean_object* v_fs_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Meta_getElimInfo(v___x_2071_, v___x_2072_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
lean_inc(v_snd_2073_);
v___x_2095_ = l_Lean_MVarId_getTag(v_snd_2073_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc(v_a_2094_);
v___x_2097_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_2094_, v___x_2074_, v_a_2096_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v_elimApp_2099_; lean_object* v_alts_2100_; lean_object* v_motivePos_2101_; lean_object* v_nargs_2102_; lean_object* v_dummy_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v_elimApp_2099_ = lean_ctor_get(v_a_2098_, 0);
lean_inc_ref_n(v_elimApp_2099_, 2);
v_alts_2100_ = lean_ctor_get(v_a_2098_, 3);
lean_inc_ref(v_alts_2100_);
lean_dec(v_a_2098_);
v_motivePos_2101_ = lean_ctor_get(v_a_2094_, 2);
lean_inc(v_motivePos_2101_);
lean_dec(v_a_2094_);
v_nargs_2102_ = l_Lean_Expr_getAppNumArgs(v_elimApp_2099_);
v_dummy_2103_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0);
lean_inc(v_nargs_2102_);
v___x_2104_ = lean_mk_array(v_nargs_2102_, v_dummy_2103_);
v___x_2105_ = lean_nat_sub(v_nargs_2102_, v___x_2075_);
lean_dec(v_nargs_2102_);
v___x_2106_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_2099_, v___x_2104_, v___x_2105_);
v___x_2107_ = lean_array_get(v___x_2076_, v___x_2106_, v_motivePos_2101_);
lean_dec(v_motivePos_2101_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = l_Lean_Expr_mvarId_x21(v___x_2107_);
lean_dec(v___x_2107_);
v___x_2109_ = l_Lean_Expr_fvarId_x21(v_e_2077_);
v___x_2110_ = lean_mk_empty_array_with_capacity(v___x_2075_);
lean_inc_ref(v___x_2110_);
v___x_2111_ = lean_array_push(v___x_2110_, v___x_2109_);
v___x_2112_ = lean_mk_empty_array_with_capacity(v___x_2078_);
lean_inc(v_snd_2073_);
v___x_2113_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_2073_, v___x_2108_, v___x_2111_, v___x_2112_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref_known(v___x_2113_, 1);
v___x_2114_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_2073_, v_elimApp_2099_, v___y_2089_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2115_ = lean_array_get_size(v_alts_2100_);
v___x_2116_ = lean_nat_dec_eq(v___x_2115_, v___x_2075_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v___x_2110_);
lean_dec_ref(v_alts_2100_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
v___x_2117_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4);
v___x_2118_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2117_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v_name_2120_; lean_object* v_mvarId_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2189_; 
v___x_2119_ = lean_array_fget(v_alts_2100_, v___x_2078_);
lean_dec_ref(v_alts_2100_);
v_name_2120_ = lean_ctor_get(v___x_2119_, 0);
v_mvarId_2121_ = lean_ctor_get(v___x_2119_, 2);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v___x_2119_, 1);
lean_dec(v_unused_2190_);
v___x_2123_ = v___x_2119_;
v_isShared_2124_ = v_isSharedCheck_2189_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_mvarId_2121_);
lean_inc(v_name_2120_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2189_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_MVarId_intro(v_mvarId_2121_, v_head_2079_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2180_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_fst_2127_ = lean_ctor_get(v_a_2126_, 0);
v_snd_2128_ = lean_ctor_get(v_a_2126_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2130_ = v_a_2126_;
v_isShared_2131_ = v_isSharedCheck_2180_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snd_2128_);
lean_inc(v_fst_2127_);
lean_dec(v_a_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2180_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_array_get_size(v_fst_2080_);
v___x_2133_ = l_Lean_Meta_introNCore(v_snd_2128_, v___x_2132_, v_tail_2081_, v___x_2082_, v___x_2116_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2171_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2171_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2171_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; lean_object* v_snd_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2170_; 
v_fst_2138_ = lean_ctor_get(v_a_2134_, 0);
v_snd_2139_ = lean_ctor_get(v_a_2134_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2141_ = v_a_2134_;
v_isShared_2142_ = v_isSharedCheck_2170_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snd_2139_);
lean_inc(v_fst_2138_);
lean_dec(v_a_2134_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2170_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___y_2144_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2164_ = l_Array_zip___redArg(v_fst_2080_, v_fst_2138_);
lean_dec(v_fst_2138_);
v___x_2165_ = lean_array_get_size(v___x_2164_);
v___x_2166_ = lean_nat_dec_lt(v___x_2078_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec_ref(v___x_2164_);
v___y_2144_ = v_fs_2085_;
goto v___jp_2143_;
}
else
{
size_t v___x_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = lean_usize_of_nat(v___x_2165_);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2164_, v___x_2167_, v___x_2168_, v_fs_2085_);
lean_dec_ref(v___x_2164_);
v___y_2144_ = v___x_2169_;
goto v___jp_2143_;
}
v___jp_2143_:
{
lean_object* v___x_2146_; 
lean_inc(v_name_2120_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v_snd_2083_);
lean_ctor_set(v___x_2141_, 0, v_name_2120_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_name_2120_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_snd_2083_);
v___x_2146_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_mkFVar(v_fst_2127_);
v___x_2150_ = lean_array_push(v___x_2084_, v___x_2149_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 2, v___y_2144_);
lean_ctor_set(v___x_2123_, 1, v___x_2150_);
lean_ctor_set(v___x_2123_, 0, v_snd_2139_);
v___x_2152_ = v___x_2123_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_snd_2139_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v___y_2144_);
v___x_2152_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_name_2120_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_array_push(v___x_2110_, v___x_2154_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v___x_2155_);
lean_ctor_set(v___x_2130_, 0, v___x_2148_);
v___x_2157_ = v___x_2130_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2157_);
v___x_2159_ = v___x_2136_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
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
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2130_);
lean_dec(v_fst_2127_);
lean_del_object(v___x_2123_);
lean_dec(v_name_2120_);
lean_dec_ref(v___x_2110_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
v_a_2172_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2133_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2133_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_del_object(v___x_2123_);
lean_dec(v_name_2120_);
lean_dec_ref(v___x_2110_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
v_a_2181_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2125_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2125_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___x_2110_);
lean_dec_ref(v_alts_2100_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
v_a_2191_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2114_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2114_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v___x_2110_);
lean_dec_ref(v_alts_2100_);
lean_dec_ref(v_elimApp_2099_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
lean_dec(v_snd_2073_);
v_a_2199_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2113_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2113_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2094_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
lean_dec(v_snd_2073_);
v_a_2207_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2097_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2097_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2094_);
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
lean_dec_ref(v___x_2074_);
lean_dec(v_snd_2073_);
v_a_2215_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2095_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2095_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_fs_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_snd_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_head_2079_);
lean_dec_ref(v___x_2074_);
lean_dec(v_snd_2073_);
v_a_2223_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2093_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2093_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2231_ = _args[0];
lean_object* v___x_2232_ = _args[1];
lean_object* v_snd_2233_ = _args[2];
lean_object* v___x_2234_ = _args[3];
lean_object* v___x_2235_ = _args[4];
lean_object* v___x_2236_ = _args[5];
lean_object* v_e_2237_ = _args[6];
lean_object* v___x_2238_ = _args[7];
lean_object* v_head_2239_ = _args[8];
lean_object* v_fst_2240_ = _args[9];
lean_object* v_tail_2241_ = _args[10];
lean_object* v___x_2242_ = _args[11];
lean_object* v_snd_2243_ = _args[12];
lean_object* v___x_2244_ = _args[13];
lean_object* v_fs_2245_ = _args[14];
lean_object* v___y_2246_ = _args[15];
lean_object* v___y_2247_ = _args[16];
lean_object* v___y_2248_ = _args[17];
lean_object* v___y_2249_ = _args[18];
lean_object* v___y_2250_ = _args[19];
lean_object* v___y_2251_ = _args[20];
lean_object* v___y_2252_ = _args[21];
_start:
{
uint8_t v___x_18847__boxed_2253_; lean_object* v_res_2254_; 
v___x_18847__boxed_2253_ = lean_unbox(v___x_2242_);
v_res_2254_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v___x_2231_, v___x_2232_, v_snd_2233_, v___x_2234_, v___x_2235_, v___x_2236_, v_e_2237_, v___x_2238_, v_head_2239_, v_fst_2240_, v_tail_2241_, v___x_18847__boxed_2253_, v_snd_2243_, v___x_2244_, v_fs_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_fst_2240_);
lean_dec(v___x_2238_);
lean_dec_ref(v_e_2237_);
lean_dec_ref(v___x_2236_);
lean_dec(v___x_2235_);
return v_res_2254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2256_ = lean_unsigned_to_nat(76u);
v___x_2257_ = lean_unsigned_to_nat(315u);
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2260_ = l_mkPanicMessageWithDecl(v___x_2259_, v___x_2258_, v___x_2257_, v___x_2256_, v___x_2255_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(uint8_t v___x_2268_, lean_object* v_e_2269_, lean_object* v___x_2270_, lean_object* v_g_2271_, lean_object* v___x_2272_, lean_object* v_fs_2273_, lean_object* v_pat_2274_, lean_object* v_____r_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2331_; lean_object* v___x_2337_; 
v___x_2337_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2274_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2331_ = v___x_2338_;
goto v___jp_2330_;
}
else
{
lean_object* v_head_2339_; 
v_head_2339_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_head_2339_);
lean_dec_ref_known(v___x_2337_, 2);
v___y_2331_ = v_head_2339_;
goto v___jp_2330_;
}
v___jp_2283_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
v___x_2285_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2284_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2285_;
}
v___jp_2286_:
{
uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_fst_2298_; 
v___x_2290_ = 0;
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2293_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1, v___x_2290_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 1, v___x_2268_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 2, v___x_2268_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 3, v___x_2268_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 4, v___x_2268_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 5, v___x_2268_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1 + 6, v___x_2268_);
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = lean_mk_empty_array_with_capacity(v___x_2294_);
lean_inc_ref(v___x_2295_);
v___x_2296_ = lean_array_push(v___x_2295_, v___x_2293_);
v___x_2297_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2289_, v___x_2296_, v___y_2287_, v___x_2291_, v___y_2288_);
lean_dec_ref(v___x_2296_);
v_fst_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_fst_2298_);
if (lean_obj_tag(v_fst_2298_) == 1)
{
lean_object* v_tail_2299_; 
v_tail_2299_ = lean_ctor_get(v_fst_2298_, 1);
lean_inc(v_tail_2299_);
if (lean_obj_tag(v_tail_2299_) == 0)
{
lean_object* v_snd_2300_; lean_object* v_head_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_snd_2300_ = lean_ctor_get(v___x_2297_, 1);
lean_inc(v_snd_2300_);
lean_dec_ref(v___x_2297_);
v_head_2301_ = lean_ctor_get(v_fst_2298_, 0);
lean_inc(v_head_2301_);
lean_dec_ref_known(v_fst_2298_, 2);
lean_inc_ref(v_e_2269_);
lean_inc_ref(v___x_2295_);
v___x_2302_ = lean_array_push(v___x_2295_, v_e_2269_);
v___x_2303_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2302_, v___x_2270_, v___x_2268_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_MVarId_revert(v_g_2271_, v_a_2304_, v___x_2268_, v___x_2268_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_fst_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___f_2312_; lean_object* v___x_2313_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_fst_2307_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_fst_2307_);
v_snd_2308_ = lean_ctor_get(v_a_2306_, 1);
lean_inc_n(v_snd_2308_, 2);
lean_dec(v_a_2306_);
v___x_2309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4));
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_box(v___x_2268_);
v___f_2312_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed), 22, 15);
lean_closure_set(v___f_2312_, 0, v___x_2309_);
lean_closure_set(v___f_2312_, 1, v___x_2310_);
lean_closure_set(v___f_2312_, 2, v_snd_2308_);
lean_closure_set(v___f_2312_, 3, v___x_2302_);
lean_closure_set(v___f_2312_, 4, v___x_2294_);
lean_closure_set(v___f_2312_, 5, v___x_2272_);
lean_closure_set(v___f_2312_, 6, v_e_2269_);
lean_closure_set(v___f_2312_, 7, v___x_2291_);
lean_closure_set(v___f_2312_, 8, v_head_2301_);
lean_closure_set(v___f_2312_, 9, v_fst_2307_);
lean_closure_set(v___f_2312_, 10, v_tail_2299_);
lean_closure_set(v___f_2312_, 11, v___x_2311_);
lean_closure_set(v___f_2312_, 12, v_snd_2300_);
lean_closure_set(v___f_2312_, 13, v___x_2295_);
lean_closure_set(v___f_2312_, 14, v_fs_2273_);
v___x_2313_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2308_, v___f_2312_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v___x_2302_);
lean_dec(v_head_2301_);
lean_dec(v_snd_2300_);
lean_dec_ref(v___x_2295_);
lean_dec(v_fs_2273_);
lean_dec_ref(v___x_2272_);
lean_dec_ref(v_e_2269_);
v_a_2314_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2305_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2305_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v___x_2302_);
lean_dec(v_head_2301_);
lean_dec(v_snd_2300_);
lean_dec_ref(v___x_2295_);
lean_dec(v_fs_2273_);
lean_dec_ref(v___x_2272_);
lean_dec(v_g_2271_);
lean_dec_ref(v_e_2269_);
v_a_2322_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2303_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2303_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_dec_ref_known(v_fst_2298_, 2);
lean_dec(v_tail_2299_);
lean_dec_ref(v___x_2297_);
lean_dec_ref(v___x_2295_);
lean_dec(v_fs_2273_);
lean_dec_ref(v___x_2272_);
lean_dec(v_g_2271_);
lean_dec(v___x_2270_);
lean_dec_ref(v_e_2269_);
goto v___jp_2283_;
}
}
else
{
lean_dec(v_fst_2298_);
lean_dec_ref(v___x_2297_);
lean_dec_ref(v___x_2295_);
lean_dec(v_fs_2273_);
lean_dec_ref(v___x_2272_);
lean_dec(v_g_2271_);
lean_dec(v___x_2270_);
lean_dec_ref(v_e_2269_);
goto v___jp_2283_;
}
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v_fst_2333_; lean_object* v_snd_2334_; lean_object* v_ref_2335_; uint8_t v___x_2336_; 
lean_inc_ref(v___y_2331_);
v___x_2332_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2331_);
v_fst_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_fst_2333_);
v_snd_2334_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_snd_2334_);
lean_dec_ref(v___x_2332_);
v_ref_2335_ = lean_ctor_get(v___y_2331_, 0);
lean_inc(v_ref_2335_);
lean_dec_ref(v___y_2331_);
v___x_2336_ = lean_unbox(v_fst_2333_);
lean_dec(v_fst_2333_);
v___y_2287_ = v___x_2336_;
v___y_2288_ = v_snd_2334_;
v___y_2289_ = v_ref_2335_;
goto v___jp_2286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object* v___x_2340_, lean_object* v_e_2341_, lean_object* v___x_2342_, lean_object* v_g_2343_, lean_object* v___x_2344_, lean_object* v_fs_2345_, lean_object* v_pat_2346_, lean_object* v_____r_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_19211__boxed_2355_; lean_object* v_res_2356_; 
v___x_19211__boxed_2355_ = lean_unbox(v___x_2340_);
v_res_2356_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_19211__boxed_2355_, v_e_2341_, v___x_2342_, v_g_2343_, v___x_2344_, v_fs_2345_, v_pat_2346_, v_____r_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2357_, lean_object* v_cont_2358_, lean_object* v_g_2359_, lean_object* v_fs_2360_, lean_object* v_clears_2361_, lean_object* v_a_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2357_, v_cont_2358_, v_g_2359_, v_fs_2360_, v_clears_2361_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2372_, lean_object* v_g_2373_, lean_object* v_fs_2374_, lean_object* v_clears_2375_, lean_object* v_a_2376_, lean_object* v_cont_2377_, lean_object* v_ref_2378_, lean_object* v_p_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; 
v___x_2387_ = lean_box(0);
lean_inc_ref(v_e_2372_);
v___x_2388_ = l_Lean_Expr_mdata___override(v___x_2387_, v_e_2372_);
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_box(0);
v___x_2391_ = 0;
v___x_2392_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2378_, v___x_2388_, v___x_2389_, v___x_2389_, v___x_2390_, v___x_2391_, v___x_2391_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref_known(v___x_2392_, 1);
v___x_2393_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2373_, v_fs_2374_, v_clears_2375_, v_e_2372_, v_a_2376_, v_p_2379_, v_cont_2377_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec_ref(v_e_2372_);
return v___x_2393_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v_p_2379_);
lean_dec_ref(v_cont_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_clears_2375_);
lean_dec(v_fs_2374_);
lean_dec(v_g_2373_);
lean_dec_ref(v_e_2372_);
v_a_2394_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2392_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
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
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2402_, lean_object* v_g_2403_, lean_object* v_fs_2404_, lean_object* v_clears_2405_, lean_object* v_a_2406_, lean_object* v_cont_2407_, lean_object* v_ref_2408_, lean_object* v_p_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2402_, v_g_2403_, v_fs_2404_, v_clears_2405_, v_a_2406_, v_cont_2407_, v_ref_2408_, v_p_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2418_, lean_object* v_clears_2419_, lean_object* v_cont_2420_, lean_object* v_a_2421_, lean_object* v_goal_2422_, lean_object* v_ctorName_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
if (lean_obj_tag(v_a_2424_) == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v_goal_2422_);
lean_dec_ref(v_cont_2420_);
lean_dec_ref(v_clears_2419_);
lean_dec(v_fs_2418_);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_a_2424_);
lean_ctor_set(v___x_2432_, 1, v_a_2421_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
else
{
lean_object* v_head_2434_; lean_object* v_tail_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2470_; 
v_head_2434_ = lean_ctor_get(v_a_2424_, 0);
lean_inc(v_head_2434_);
v_tail_2435_ = lean_ctor_get(v_a_2424_, 1);
lean_inc(v_tail_2435_);
lean_dec_ref_known(v_a_2424_, 2);
v_fst_2436_ = lean_ctor_get(v_head_2434_, 0);
v_snd_2437_ = lean_ctor_get(v_head_2434_, 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_head_2434_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2439_ = v_head_2434_;
v_isShared_2440_ = v_isSharedCheck_2470_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snd_2437_);
lean_inc(v_fst_2436_);
lean_dec(v_head_2434_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2470_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_fst_2436_);
v___x_2442_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2441_, v_ctorName_2423_);
lean_dec_ref_known(v___x_2441_, 1);
if (v___x_2442_ == 0)
{
lean_del_object(v___x_2439_);
lean_dec(v_snd_2437_);
v_a_2424_ = v_tail_2435_;
goto _start;
}
else
{
lean_object* v_mvarId_2444_; lean_object* v_fields_2445_; lean_object* v_subst_2446_; lean_object* v_fs_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_mvarId_2444_ = lean_ctor_get(v_goal_2422_, 0);
lean_inc(v_mvarId_2444_);
v_fields_2445_ = lean_ctor_get(v_goal_2422_, 1);
lean_inc_ref(v_fields_2445_);
v_subst_2446_ = lean_ctor_get(v_goal_2422_, 2);
lean_inc(v_subst_2446_);
lean_dec_ref(v_goal_2422_);
v_fs_2447_ = l_Lean_Meta_FVarSubst_append(v_fs_2418_, v_subst_2446_);
v___x_2448_ = lean_array_to_list(v_fields_2445_);
v___x_2449_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_snd_2437_, v___x_2448_);
v___x_2450_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2444_, v_fs_2447_, v_clears_2419_, v_a_2421_, v___x_2449_, v_cont_2420_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2461_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v_a_2451_);
lean_ctor_set(v___x_2439_, 0, v_tail_2435_);
v___x_2456_ = v___x_2439_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_tail_2435_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2458_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2456_);
v___x_2458_ = v___x_2453_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_del_object(v___x_2439_);
lean_dec(v_tail_2435_);
v_a_2462_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2450_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2450_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2471_, lean_object* v_clears_2472_, lean_object* v_cont_2473_, lean_object* v_as_2474_, size_t v_i_2475_, size_t v_stop_2476_, lean_object* v_b_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2475_, v_stop_2476_);
if (v___x_2485_ == 0)
{
lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2488_; lean_object* v_toInductionSubgoal_2489_; lean_object* v_ctorName_2490_; lean_object* v___x_2491_; 
v_fst_2486_ = lean_ctor_get(v_b_2477_, 0);
lean_inc(v_fst_2486_);
v_snd_2487_ = lean_ctor_get(v_b_2477_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v_b_2477_);
v___x_2488_ = lean_array_uget_borrowed(v_as_2474_, v_i_2475_);
v_toInductionSubgoal_2489_ = lean_ctor_get(v___x_2488_, 0);
v_ctorName_2490_ = lean_ctor_get(v___x_2488_, 1);
lean_inc_ref(v_toInductionSubgoal_2489_);
lean_inc_ref(v_cont_2473_);
lean_inc_ref(v_clears_2472_);
lean_inc(v_fs_2471_);
v___x_2491_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2471_, v_clears_2472_, v_cont_2473_, v_snd_2487_, v_toInductionSubgoal_2489_, v_ctorName_2490_, v_fst_2486_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; size_t v___x_2493_; size_t v___x_2494_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_add(v_i_2475_, v___x_2493_);
v_i_2475_ = v___x_2494_;
v_b_2477_ = v_a_2492_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2473_);
lean_dec_ref(v_clears_2472_);
lean_dec(v_fs_2471_);
return v___x_2491_;
}
}
else
{
lean_object* v___x_2496_; 
lean_dec_ref(v_cont_2473_);
lean_dec_ref(v_clears_2472_);
lean_dec(v_fs_2471_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_b_2477_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_a_2499_, lean_object* v_fs_2500_, lean_object* v_clears_2501_, lean_object* v_cont_2502_, lean_object* v_e_2503_, lean_object* v___x_2504_, lean_object* v_g_2505_, lean_object* v___x_2506_, lean_object* v_pat_2507_, lean_object* v___y_2508_, lean_object* v_asFVar_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___y_2547_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2559_ = lean_box(0);
lean_inc_ref(v_e_2503_);
v___x_2560_ = l_Lean_Expr_mdata___override(v___x_2559_, v_e_2503_);
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_box(0);
v___x_2563_ = 0;
lean_inc(v___y_2508_);
v___x_2564_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2508_, v___x_2560_, v___x_2561_, v___x_2561_, v___x_2562_, v___x_2563_, v___x_2563_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref_known(v___x_2564_, 1);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc_ref(v_e_2503_);
v___x_2565_ = lean_apply_6(v_asFVar_2509_, v_e_2503_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2566_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2563_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2566_, 1);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc_ref(v_e_2503_);
v___x_2567_ = lean_infer_type(v_e_2503_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = l_Lean_Meta_whnfD(v_a_2568_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_Expr_getAppFn(v_a_2570_);
if (lean_obj_tag(v___x_2571_) == 4)
{
lean_object* v_declName_2572_; lean_object* v___x_2573_; lean_object* v_env_2574_; lean_object* v___x_2575_; 
v_declName_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_declName_2572_);
lean_dec_ref_known(v___x_2571_, 2);
v___x_2573_ = lean_st_ref_get(v___y_2516_);
v_env_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_ref(v_env_2574_);
lean_dec(v___x_2573_);
v___x_2575_ = l_Lean_Environment_find_x3f(v_env_2574_, v_declName_2572_, v___x_2563_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
v___x_2576_ = lean_box(0);
v___x_2577_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2503_, v_a_2570_, lean_box(0), v___x_2576_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v___y_2547_ = v___x_2577_;
goto v___jp_2546_;
}
else
{
lean_object* v_val_2578_; 
v_val_2578_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2575_, 1);
switch(lean_obj_tag(v_val_2578_))
{
case 4:
{
lean_object* v_val_2579_; uint8_t v_kind_2580_; 
lean_dec(v___y_2508_);
v_val_2579_ = lean_ctor_get(v_val_2578_, 0);
lean_inc_ref(v_val_2579_);
lean_dec_ref_known(v_val_2578_, 1);
v_kind_2580_ = lean_ctor_get_uint8(v_val_2579_, sizeof(void*)*1);
lean_dec_ref(v_val_2579_);
if (v_kind_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec(v_a_2570_);
v___x_2581_ = lean_box(0);
lean_inc(v_fs_2500_);
v___x_2582_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2563_, v_e_2503_, v___x_2504_, v_g_2505_, v___x_2506_, v_fs_2500_, v_pat_2507_, v___x_2581_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v___y_2547_ = v___x_2582_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_box(0);
lean_inc_ref(v_e_2503_);
v___x_2584_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2503_, v_a_2570_, lean_box(0), v___x_2583_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
lean_inc(v_fs_2500_);
v___x_2586_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2563_, v_e_2503_, v___x_2504_, v_g_2505_, v___x_2506_, v_fs_2500_, v_pat_2507_, v_a_2585_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v___y_2547_ = v___x_2586_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2587_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2584_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2584_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
case 5:
{
lean_object* v_val_2595_; lean_object* v_numParams_2596_; lean_object* v_ctors_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_a_2570_);
lean_dec_ref(v___x_2506_);
lean_dec(v___x_2504_);
v_val_2595_ = lean_ctor_get(v_val_2578_, 0);
lean_inc_ref(v_val_2595_);
lean_dec_ref_known(v_val_2578_, 1);
v_numParams_2596_ = lean_ctor_get(v_val_2595_, 1);
lean_inc(v_numParams_2596_);
v_ctors_2597_ = lean_ctor_get(v_val_2595_, 4);
lean_inc(v_ctors_2597_);
lean_dec_ref(v_val_2595_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2599_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2507_);
v___x_2600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2508_, v_numParams_2596_, v___x_2598_, v_ctors_2597_, v___x_2599_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v_numParams_2596_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v_fst_2602_; lean_object* v_snd_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v_fst_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_fst_2602_);
v_snd_2603_ = lean_ctor_get(v_a_2601_, 1);
lean_inc(v_snd_2603_);
lean_dec(v_a_2601_);
v___x_2604_ = l_Lean_Expr_fvarId_x21(v_e_2503_);
lean_dec_ref(v_e_2503_);
v___x_2605_ = 1;
v___x_2606_ = l_Lean_MVarId_cases(v_g_2505_, v___x_2604_, v_fst_2602_, v___x_2605_, v___x_2561_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v_fst_2519_ = v_snd_2603_;
v_snd_2520_ = v_a_2607_;
goto v___jp_2518_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_snd_2603_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2608_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2606_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2606_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_g_2505_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2616_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2600_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2600_);
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
default: 
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec(v_val_2578_);
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
v___x_2624_ = lean_box(0);
v___x_2625_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2503_, v_a_2570_, lean_box(0), v___x_2624_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v___y_2547_ = v___x_2625_;
goto v___jp_2546_;
}
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v___x_2571_);
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
v___x_2626_ = lean_box(0);
v___x_2627_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2503_, v_a_2570_, lean_box(0), v___x_2626_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
v___y_2547_ = v___x_2627_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2628_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2569_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2569_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2636_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2567_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2567_);
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
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2644_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2566_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2566_);
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
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2652_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2565_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2565_);
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
lean_dec_ref(v_asFVar_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v_pat_2507_);
lean_dec_ref(v___x_2506_);
lean_dec(v_g_2505_);
lean_dec(v___x_2504_);
lean_dec_ref(v_e_2503_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2660_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2564_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2564_);
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
v___jp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_array_get_size(v_snd_2520_);
v___x_2523_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v_snd_2520_);
lean_dec(v_fst_2519_);
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_a_2499_);
return v___x_2524_;
}
else
{
lean_object* v___x_2525_; size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_fst_2519_);
lean_ctor_set(v___x_2525_, 1, v_a_2499_);
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2522_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2500_, v_clears_2501_, v_cont_2502_, v_snd_2520_, v___x_2526_, v___x_2527_, v___x_2525_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec_ref(v_snd_2520_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_snd_2533_; lean_object* v___x_2535_; 
v_snd_2533_ = lean_ctor_get(v_a_2529_, 1);
lean_inc(v_snd_2533_);
lean_dec(v_a_2529_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v_snd_2533_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_snd_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2528_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2528_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v_fst_2549_; lean_object* v_snd_2550_; 
v_a_2548_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___y_2547_, 1);
v_fst_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_fst_2549_);
v_snd_2550_ = lean_ctor_get(v_a_2548_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_a_2548_);
v_fst_2519_ = v_fst_2549_;
v_snd_2520_ = v_snd_2550_;
goto v___jp_2518_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_cont_2502_);
lean_dec_ref(v_clears_2501_);
lean_dec(v_fs_2500_);
lean_dec(v_a_2499_);
v_a_2551_ = lean_ctor_get(v___y_2547_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___y_2547_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___y_2547_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___y_2547_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_a_2668_ = _args[0];
lean_object* v_fs_2669_ = _args[1];
lean_object* v_clears_2670_ = _args[2];
lean_object* v_cont_2671_ = _args[3];
lean_object* v_e_2672_ = _args[4];
lean_object* v___x_2673_ = _args[5];
lean_object* v_g_2674_ = _args[6];
lean_object* v___x_2675_ = _args[7];
lean_object* v_pat_2676_ = _args[8];
lean_object* v___y_2677_ = _args[9];
lean_object* v_asFVar_2678_ = _args[10];
lean_object* v_x_2679_ = _args[11];
lean_object* v___y_2680_ = _args[12];
lean_object* v___y_2681_ = _args[13];
lean_object* v___y_2682_ = _args[14];
lean_object* v___y_2683_ = _args[15];
lean_object* v___y_2684_ = _args[16];
lean_object* v___y_2685_ = _args[17];
lean_object* v___y_2686_ = _args[18];
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_a_2668_, v_fs_2669_, v_clears_2670_, v_cont_2671_, v_e_2672_, v___x_2673_, v_g_2674_, v___x_2675_, v_pat_2676_, v___y_2677_, v_asFVar_2678_, v_x_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_x_2679_);
return v_res_2687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2692_ = l_Lean_MessageData_ofFormat(v___x_2691_);
return v___x_2692_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2695_, lean_object* v___f_2696_, lean_object* v_e_2697_, lean_object* v_asFVar_2698_, lean_object* v_g_2699_, lean_object* v_fs_2700_, lean_object* v_cont_2701_, lean_object* v_clears_2702_, lean_object* v_a_2703_, lean_object* v___f_2704_, lean_object* v___f_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
switch(lean_obj_tag(v_pat_2695_))
{
case 1:
{
lean_object* v_a_2713_; 
lean_dec_ref(v___f_2705_);
lean_dec_ref(v___f_2704_);
v_a_2713_ = lean_ctor_get(v_pat_2695_, 1);
lean_inc(v_a_2713_);
if (lean_obj_tag(v_a_2713_) == 1)
{
lean_object* v_pre_2714_; 
v_pre_2714_ = lean_ctor_get(v_a_2713_, 0);
if (lean_obj_tag(v_pre_2714_) == 0)
{
lean_object* v_ref_2715_; lean_object* v_str_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_ref_2715_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2715_);
lean_dec_ref_known(v_pat_2695_, 2);
v_str_2716_ = lean_ctor_get(v_a_2713_, 1);
v___x_2717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2718_ = lean_string_dec_eq(v_str_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2719_ = lean_apply_9(v___f_2696_, v_ref_2715_, v_a_2713_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2719_;
}
else
{
uint8_t v___x_2720_; lean_object* v___x_2721_; 
lean_inc(v_pre_2714_);
lean_dec_ref_known(v_a_2713_, 2);
lean_dec_ref(v___f_2696_);
v___x_2720_ = 0;
v___x_2721_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2720_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref_known(v___x_2721_, 1);
v___x_2722_ = lean_box(0);
lean_inc_ref(v_e_2697_);
v___x_2723_ = l_Lean_Expr_mdata___override(v___x_2722_, v_e_2697_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2715_, v___x_2723_, v___x_2724_, v___x_2724_, v_pre_2714_, v___x_2720_, v___x_2720_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2726_; 
lean_dec_ref_known(v___x_2725_, 1);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2726_ = lean_apply_6(v_asFVar_2698_, v_e_2697_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = l_Lean_Meta_substEq(v_g_2699_, v_a_2727_, v_fs_2700_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v_fst_2730_; lean_object* v_snd_2731_; lean_object* v___x_2732_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v_fst_2730_ = lean_ctor_get(v_a_2729_, 0);
lean_inc(v_fst_2730_);
v_snd_2731_ = lean_ctor_get(v_a_2729_, 1);
lean_inc(v_snd_2731_);
lean_dec(v_a_2729_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2732_ = lean_apply_11(v_cont_2701_, v_snd_2731_, v_fst_2730_, v_clears_2702_, v_a_2703_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2732_;
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
v_a_2733_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2728_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
v_a_2741_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2726_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2726_);
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
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
v_a_2749_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2725_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2725_);
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
lean_dec(v_ref_2715_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
v_a_2757_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2721_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2721_);
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
}
else
{
lean_object* v_ref_2765_; lean_object* v___x_2766_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
v_ref_2765_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2765_);
lean_dec_ref_known(v_pat_2695_, 2);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2766_ = lean_apply_9(v___f_2696_, v_ref_2765_, v_a_2713_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2766_;
}
}
else
{
lean_object* v_ref_2767_; lean_object* v___x_2768_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
v_ref_2767_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2767_);
lean_dec_ref_known(v_pat_2695_, 2);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2768_ = lean_apply_9(v___f_2696_, v_ref_2767_, v_a_2713_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2768_;
}
}
case 2:
{
lean_object* v_ref_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; 
lean_dec_ref(v___f_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v___f_2696_);
v_ref_2769_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2769_);
lean_dec_ref_known(v_pat_2695_, 1);
v___x_2770_ = lean_box(0);
lean_inc_ref(v_e_2697_);
v___x_2771_ = l_Lean_Expr_mdata___override(v___x_2770_, v_e_2697_);
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_box(0);
v___x_2774_ = 0;
v___x_2775_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2769_, v___x_2771_, v___x_2772_, v___x_2772_, v___x_2773_, v___x_2774_, v___x_2774_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_dec_ref_known(v___x_2775_, 1);
if (lean_obj_tag(v_e_2697_) == 1)
{
lean_object* v_fvarId_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_fvarId_2776_ = lean_ctor_get(v_e_2697_, 0);
lean_inc(v_fvarId_2776_);
lean_dec_ref_known(v_e_2697_, 1);
v___x_2777_ = lean_array_push(v_clears_2702_, v_fvarId_2776_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2778_ = lean_apply_11(v_cont_2701_, v_g_2699_, v_fs_2700_, v___x_2777_, v_a_2703_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; 
lean_dec_ref(v_e_2697_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2779_ = lean_apply_11(v_cont_2701_, v_g_2699_, v_fs_2700_, v_clears_2702_, v_a_2703_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2779_;
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2780_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2775_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2775_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
case 4:
{
lean_object* v_ref_2788_; lean_object* v_a_2789_; lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; 
lean_dec_ref(v___f_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v___f_2696_);
v_ref_2788_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2788_);
v_a_2789_ = lean_ctor_get(v_pat_2695_, 1);
lean_inc_ref(v_a_2789_);
v_a_2790_ = lean_ctor_get(v_pat_2695_, 2);
lean_inc(v_a_2790_);
lean_dec_ref_known(v_pat_2695_, 3);
v___x_2791_ = lean_box(0);
lean_inc_ref(v_e_2697_);
v___x_2792_ = l_Lean_Expr_mdata___override(v___x_2791_, v_e_2697_);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_box(0);
v___x_2795_ = 0;
v___x_2796_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2788_, v___x_2792_, v___x_2793_, v___x_2793_, v___x_2794_, v___x_2795_, v___x_2795_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2797_; 
lean_dec_ref_known(v___x_2796_, 1);
v___x_2797_ = l_Lean_Elab_Term_elabType(v_a_2790_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___x_2819_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc_ref(v_e_2697_);
v___x_2819_ = lean_infer_type(v_e_2697_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc_n(v_a_2820_, 2);
lean_dec_ref_known(v___x_2819_, 1);
lean_inc(v_a_2798_);
v___x_2821_ = l_Lean_Meta_isExprDefEq(v_a_2820_, v_a_2798_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; uint8_t v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = lean_unbox(v_a_2822_);
lean_dec(v_a_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2697_);
lean_inc(v_a_2798_);
v___x_2825_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2824_, v_a_2798_, v_a_2820_, v_e_2697_, v___x_2793_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
v___y_2800_ = v___y_2706_;
v___y_2801_ = v___y_2707_;
v___y_2802_ = v___y_2708_;
v___y_2803_ = v___y_2709_;
v___y_2804_ = v___y_2710_;
v___y_2805_ = v___y_2711_;
goto v___jp_2799_;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_dec(v_a_2820_);
v___y_2800_ = v___y_2706_;
v___y_2801_ = v___y_2707_;
v___y_2802_ = v___y_2708_;
v___y_2803_ = v___y_2709_;
v___y_2804_ = v___y_2710_;
v___y_2805_ = v___y_2711_;
goto v___jp_2799_;
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2820_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2834_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2821_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2821_);
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
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2842_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2819_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2819_);
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
v___jp_2799_:
{
if (lean_obj_tag(v_e_2697_) == 1)
{
lean_object* v_fvarId_2806_; lean_object* v___x_2807_; 
v_fvarId_2806_ = lean_ctor_get(v_e_2697_, 0);
lean_inc(v_fvarId_2806_);
v___x_2807_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2699_, v_fvarId_2806_, v_a_2798_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2808_, v_fs_2700_, v_clears_2702_, v_e_2697_, v_a_2703_, v_a_2789_, v_cont_2701_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec_ref_known(v_e_2697_, 1);
return v___x_2809_;
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref_known(v_e_2697_, 1);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
v_a_2810_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2807_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2807_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v___x_2818_; 
lean_dec(v_a_2798_);
v___x_2818_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2699_, v_fs_2700_, v_clears_2702_, v_e_2697_, v_a_2703_, v_a_2789_, v_cont_2701_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec_ref(v_e_2697_);
return v___x_2818_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2850_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2797_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2797_);
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
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_e_2697_);
v_a_2858_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2796_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2796_);
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
case 0:
{
lean_object* v_ref_2866_; lean_object* v_a_2867_; lean_object* v___x_2868_; 
lean_dec_ref(v___f_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
lean_dec_ref(v___f_2696_);
v_ref_2866_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2866_);
v_a_2867_ = lean_ctor_get(v_pat_2695_, 1);
lean_inc_ref(v_a_2867_);
lean_dec_ref_known(v_pat_2695_, 2);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2868_ = lean_apply_9(v___f_2704_, v_ref_2866_, v_a_2867_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2868_;
}
case 6:
{
lean_object* v_a_2869_; 
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
lean_dec_ref(v___f_2696_);
v_a_2869_ = lean_ctor_get(v_pat_2695_, 1);
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_tail_2870_; 
v_tail_2870_ = lean_ctor_get(v_a_2869_, 1);
if (lean_obj_tag(v_tail_2870_) == 0)
{
lean_object* v_ref_2871_; lean_object* v_head_2872_; lean_object* v___x_2873_; 
lean_inc_ref(v_a_2869_);
lean_dec_ref(v___f_2705_);
v_ref_2871_ = lean_ctor_get(v_pat_2695_, 0);
lean_inc(v_ref_2871_);
lean_dec_ref_known(v_pat_2695_, 2);
v_head_2872_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_head_2872_);
lean_dec_ref_known(v_a_2869_, 2);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2873_ = lean_apply_9(v___f_2704_, v_ref_2871_, v_head_2872_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; 
lean_dec_ref(v___f_2704_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2874_ = lean_apply_8(v___f_2705_, v_pat_2695_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2874_;
}
}
else
{
lean_object* v___x_2875_; 
lean_dec_ref(v___f_2704_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2875_ = lean_apply_8(v___f_2705_, v_pat_2695_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2875_;
}
}
default: 
{
lean_object* v___x_2876_; 
lean_dec_ref(v___f_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_clears_2702_);
lean_dec_ref(v_cont_2701_);
lean_dec(v_fs_2700_);
lean_dec(v_g_2699_);
lean_dec_ref(v_asFVar_2698_);
lean_dec_ref(v_e_2697_);
lean_dec_ref(v___f_2696_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
v___x_2876_ = lean_apply_8(v___f_2705_, v_pat_2695_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, lean_box(0));
return v___x_2876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2877_ = _args[0];
lean_object* v___f_2878_ = _args[1];
lean_object* v_e_2879_ = _args[2];
lean_object* v_asFVar_2880_ = _args[3];
lean_object* v_g_2881_ = _args[4];
lean_object* v_fs_2882_ = _args[5];
lean_object* v_cont_2883_ = _args[6];
lean_object* v_clears_2884_ = _args[7];
lean_object* v_a_2885_ = _args[8];
lean_object* v___f_2886_ = _args[9];
lean_object* v___f_2887_ = _args[10];
lean_object* v___y_2888_ = _args[11];
lean_object* v___y_2889_ = _args[12];
lean_object* v___y_2890_ = _args[13];
lean_object* v___y_2891_ = _args[14];
lean_object* v___y_2892_ = _args[15];
lean_object* v___y_2893_ = _args[16];
lean_object* v___y_2894_ = _args[17];
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2877_, v___f_2878_, v_e_2879_, v_asFVar_2880_, v_g_2881_, v_fs_2882_, v_cont_2883_, v_clears_2884_, v_a_2885_, v___f_2886_, v___f_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2896_, lean_object* v_fs_2897_, lean_object* v_clears_2898_, lean_object* v_e_2899_, lean_object* v_a_2900_, lean_object* v_pat_2901_, lean_object* v_cont_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_asFVar_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_e_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___y_2917_; lean_object* v_ref_2929_; 
v_asFVar_2910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2911_ = lean_box(1);
v___x_2912_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2897_, 3);
v_e_2913_ = l_Lean_Meta_FVarSubst_apply(v_fs_2897_, v_e_2899_);
lean_inc_n(v_a_2900_, 2);
lean_inc_ref_n(v_clears_2898_, 2);
lean_inc_n(v_g_2896_, 2);
lean_inc_ref_n(v_cont_2902_, 2);
lean_inc_ref_n(v_e_2913_, 2);
v___f_2914_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2914_, 0, v_e_2913_);
lean_closure_set(v___f_2914_, 1, v_cont_2902_);
lean_closure_set(v___f_2914_, 2, v_g_2896_);
lean_closure_set(v___f_2914_, 3, v_fs_2897_);
lean_closure_set(v___f_2914_, 4, v_clears_2898_);
lean_closure_set(v___f_2914_, 5, v_a_2900_);
v___f_2915_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2915_, 0, v_e_2913_);
lean_closure_set(v___f_2915_, 1, v_g_2896_);
lean_closure_set(v___f_2915_, 2, v_fs_2897_);
lean_closure_set(v___f_2915_, 3, v_clears_2898_);
lean_closure_set(v___f_2915_, 4, v_a_2900_);
lean_closure_set(v___f_2915_, 5, v_cont_2902_);
v_ref_2929_ = lean_ctor_get(v_pat_2901_, 0);
lean_inc(v_ref_2929_);
v___y_2917_ = v_ref_2929_;
goto v___jp_2916_;
v___jp_2916_:
{
lean_object* v_toCold_2918_; lean_object* v_currRecDepth_2919_; lean_object* v_ref_2920_; uint16_t v_optionFlags_2921_; uint8_t v_suppressElabErrors_2922_; uint8_t v_isRecordingDeps_2923_; lean_object* v___f_2924_; lean_object* v___y_2925_; lean_object* v_ref_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_toCold_2918_ = lean_ctor_get(v_a_2907_, 0);
v_currRecDepth_2919_ = lean_ctor_get(v_a_2907_, 1);
v_ref_2920_ = lean_ctor_get(v_a_2907_, 2);
v_optionFlags_2921_ = lean_ctor_get_uint16(v_a_2907_, sizeof(void*)*3);
v_suppressElabErrors_2922_ = lean_ctor_get_uint8(v_a_2907_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2923_ = lean_ctor_get_uint8(v_a_2907_, sizeof(void*)*3 + 3);
lean_inc(v___y_2917_);
lean_inc_ref(v_pat_2901_);
lean_inc_n(v_g_2896_, 2);
lean_inc_ref(v_e_2913_);
lean_inc_ref(v_cont_2902_);
lean_inc_ref(v_clears_2898_);
lean_inc(v_fs_2897_);
lean_inc(v_a_2900_);
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2924_, 0, v_a_2900_);
lean_closure_set(v___f_2924_, 1, v_fs_2897_);
lean_closure_set(v___f_2924_, 2, v_clears_2898_);
lean_closure_set(v___f_2924_, 3, v_cont_2902_);
lean_closure_set(v___f_2924_, 4, v_e_2913_);
lean_closure_set(v___f_2924_, 5, v___x_2911_);
lean_closure_set(v___f_2924_, 6, v_g_2896_);
lean_closure_set(v___f_2924_, 7, v___x_2912_);
lean_closure_set(v___f_2924_, 8, v_pat_2901_);
lean_closure_set(v___f_2924_, 9, v___y_2917_);
lean_closure_set(v___f_2924_, 10, v_asFVar_2910_);
v___y_2925_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2925_, 0, v_pat_2901_);
lean_closure_set(v___y_2925_, 1, v___f_2914_);
lean_closure_set(v___y_2925_, 2, v_e_2913_);
lean_closure_set(v___y_2925_, 3, v_asFVar_2910_);
lean_closure_set(v___y_2925_, 4, v_g_2896_);
lean_closure_set(v___y_2925_, 5, v_fs_2897_);
lean_closure_set(v___y_2925_, 6, v_cont_2902_);
lean_closure_set(v___y_2925_, 7, v_clears_2898_);
lean_closure_set(v___y_2925_, 8, v_a_2900_);
lean_closure_set(v___y_2925_, 9, v___f_2915_);
lean_closure_set(v___y_2925_, 10, v___f_2924_);
v_ref_2926_ = l_Lean_replaceRef(v___y_2917_, v_ref_2920_);
lean_dec(v___y_2917_);
lean_inc(v_currRecDepth_2919_);
lean_inc_ref(v_toCold_2918_);
v___x_2927_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2927_, 0, v_toCold_2918_);
lean_ctor_set(v___x_2927_, 1, v_currRecDepth_2919_);
lean_ctor_set(v___x_2927_, 2, v_ref_2926_);
lean_ctor_set_uint16(v___x_2927_, sizeof(void*)*3, v_optionFlags_2921_);
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*3 + 2, v_suppressElabErrors_2922_);
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*3 + 3, v_isRecordingDeps_2923_);
v___x_2928_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2896_, v___y_2925_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v___x_2927_, v_a_2908_);
lean_dec_ref_known(v___x_2927_, 3);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2930_, lean_object* v_fs_2931_, lean_object* v_clears_2932_, lean_object* v_a_2933_, lean_object* v_pats_2934_, lean_object* v_cont_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
if (lean_obj_tag(v_pats_2934_) == 0)
{
lean_object* v___x_2943_; 
lean_inc(v_a_2941_);
lean_inc_ref(v_a_2940_);
lean_inc(v_a_2939_);
lean_inc_ref(v_a_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_a_2936_);
v___x_2943_ = lean_apply_11(v_cont_2935_, v_g_2930_, v_fs_2931_, v_clears_2932_, v_a_2933_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, lean_box(0));
return v___x_2943_;
}
else
{
lean_object* v_head_2944_; lean_object* v_tail_2945_; lean_object* v_fst_2946_; lean_object* v_snd_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; 
v_head_2944_ = lean_ctor_get(v_pats_2934_, 0);
lean_inc(v_head_2944_);
v_tail_2945_ = lean_ctor_get(v_pats_2934_, 1);
lean_inc(v_tail_2945_);
lean_dec_ref_known(v_pats_2934_, 2);
v_fst_2946_ = lean_ctor_get(v_head_2944_, 0);
lean_inc(v_fst_2946_);
v_snd_2947_ = lean_ctor_get(v_head_2944_, 1);
lean_inc(v_snd_2947_);
lean_dec(v_head_2944_);
v___f_2948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2948_, 0, v_tail_2945_);
lean_closure_set(v___f_2948_, 1, v_cont_2935_);
v___x_2949_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2930_, v_fs_2931_, v_clears_2932_, v_snd_2947_, v_a_2933_, v_fst_2946_, v___f_2948_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_snd_2947_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2950_, lean_object* v_cont_2951_, lean_object* v_g_2952_, lean_object* v_fs_2953_, lean_object* v_clears_2954_, lean_object* v_a_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2952_, v_fs_2953_, v_clears_2954_, v_a_2955_, v_tail_2950_, v_cont_2951_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2964_, lean_object* v_fs_2965_, lean_object* v_clears_2966_, lean_object* v_a_2967_, lean_object* v_pats_2968_, lean_object* v_cont_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2964_, v_fs_2965_, v_clears_2966_, v_a_2967_, v_pats_2968_, v_cont_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_2978_, lean_object* v_clears_2979_, lean_object* v_cont_2980_, lean_object* v_as_2981_, lean_object* v_i_2982_, lean_object* v_stop_2983_, lean_object* v_b_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
size_t v_i_boxed_2992_; size_t v_stop_boxed_2993_; lean_object* v_res_2994_; 
v_i_boxed_2992_ = lean_unbox_usize(v_i_2982_);
lean_dec(v_i_2982_);
v_stop_boxed_2993_ = lean_unbox_usize(v_stop_2983_);
lean_dec(v_stop_2983_);
v_res_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2978_, v_clears_2979_, v_cont_2980_, v_as_2981_, v_i_boxed_2992_, v_stop_boxed_2993_, v_b_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_as_2981_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_2995_, lean_object* v_clears_2996_, lean_object* v_cont_2997_, lean_object* v_a_2998_, lean_object* v_goal_2999_, lean_object* v_ctorName_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2995_, v_clears_2996_, v_cont_2997_, v_a_2998_, v_goal_2999_, v_ctorName_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec(v_ctorName_3000_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3010_, lean_object* v_fs_3011_, lean_object* v_clears_3012_, lean_object* v_e_3013_, lean_object* v_a_3014_, lean_object* v_pat_3015_, lean_object* v_cont_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3010_, v_fs_3011_, v_clears_3012_, v_e_3013_, v_a_3014_, v_pat_3015_, v_cont_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v_e_3013_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3025_, lean_object* v_g_3026_, lean_object* v_fs_3027_, lean_object* v_clears_3028_, lean_object* v_a_3029_, lean_object* v_pats_3030_, lean_object* v_cont_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3026_, v_fs_3027_, v_clears_3028_, v_a_3029_, v_pats_3030_, v_cont_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_g_3041_, lean_object* v_fs_3042_, lean_object* v_clears_3043_, lean_object* v_a_3044_, lean_object* v_pats_3045_, lean_object* v_cont_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3040_, v_g_3041_, v_fs_3042_, v_clears_3043_, v_a_3044_, v_pats_3045_, v_cont_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3055_, lean_object* v_fs_3056_, lean_object* v_clears_3057_, lean_object* v_cont_3058_, lean_object* v_a_3059_, lean_object* v_goal_3060_, lean_object* v_ctorName_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3056_, v_clears_3057_, v_cont_3058_, v_a_3059_, v_goal_3060_, v_ctorName_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3071_, lean_object* v_fs_3072_, lean_object* v_clears_3073_, lean_object* v_cont_3074_, lean_object* v_a_3075_, lean_object* v_goal_3076_, lean_object* v_ctorName_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3071_, v_fs_3072_, v_clears_3073_, v_cont_3074_, v_a_3075_, v_goal_3076_, v_ctorName_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_ctorName_3077_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3087_, lean_object* v_mvarId_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3088_, v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_mvarId_3099_, lean_object* v_x_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3098_, v_mvarId_3099_, v_x_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3109_, lean_object* v_g_3110_, lean_object* v_fs_3111_, lean_object* v_clears_3112_, lean_object* v_e_3113_, lean_object* v_a_3114_, lean_object* v_pat_3115_, lean_object* v_cont_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3110_, v_fs_3111_, v_clears_3112_, v_e_3113_, v_a_3114_, v_pat_3115_, v_cont_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_g_3126_, lean_object* v_fs_3127_, lean_object* v_clears_3128_, lean_object* v_e_3129_, lean_object* v_a_3130_, lean_object* v_pat_3131_, lean_object* v_cont_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3125_, v_g_3126_, v_fs_3127_, v_clears_3128_, v_e_3129_, v_a_3130_, v_pat_3131_, v_cont_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec_ref(v_e_3129_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3141_, lean_object* v_fs_3142_, lean_object* v_clears_3143_, lean_object* v_cont_3144_, lean_object* v_as_3145_, size_t v_i_3146_, size_t v_stop_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3142_, v_clears_3143_, v_cont_3144_, v_as_3145_, v_i_3146_, v_stop_3147_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_fs_3158_, lean_object* v_clears_3159_, lean_object* v_cont_3160_, lean_object* v_as_3161_, lean_object* v_i_3162_, lean_object* v_stop_3163_, lean_object* v_b_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
size_t v_i_boxed_3172_; size_t v_stop_boxed_3173_; lean_object* v_res_3174_; 
v_i_boxed_3172_ = lean_unbox_usize(v_i_3162_);
lean_dec(v_i_3162_);
v_stop_boxed_3173_ = lean_unbox_usize(v_stop_3163_);
lean_dec(v_stop_3163_);
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3157_, v_fs_3158_, v_clears_3159_, v_cont_3160_, v_as_3161_, v_i_boxed_3172_, v_stop_boxed_3173_, v_b_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v_as_3161_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3175_, lean_object* v_val_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3175_, v_val_3176_, v___y_3180_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3185_, lean_object* v_val_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3185_, v_val_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3195_, lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3205_, v_msg_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3216_, v_x_3217_, v_x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3220_, lean_object* v_macroStack_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3220_, v_macroStack_3221_, v___y_3226_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3230_, lean_object* v_macroStack_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3230_, v_macroStack_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3240_, lean_object* v_x_3241_, size_t v_x_3242_, size_t v_x_3243_, lean_object* v_x_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3241_, v_x_3242_, v_x_3243_, v_x_3244_, v_x_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
size_t v_x_20511__boxed_3253_; size_t v_x_20512__boxed_3254_; lean_object* v_res_3255_; 
v_x_20511__boxed_3253_ = lean_unbox_usize(v_x_3249_);
lean_dec(v_x_3249_);
v_x_20512__boxed_3254_ = lean_unbox_usize(v_x_3250_);
lean_dec(v_x_3250_);
v_res_3255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3247_, v_x_3248_, v_x_20511__boxed_3253_, v_x_20512__boxed_3254_, v_x_3251_, v_x_3252_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3256_, lean_object* v_n_3257_, lean_object* v_k_3258_, lean_object* v_v_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3257_, v_k_3258_, v_v_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3261_, size_t v_depth_3262_, lean_object* v_keys_3263_, lean_object* v_vals_3264_, lean_object* v_heq_3265_, lean_object* v_i_3266_, lean_object* v_entries_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3262_, v_keys_3263_, v_vals_3264_, v_i_3266_, v_entries_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_depth_3270_, lean_object* v_keys_3271_, lean_object* v_vals_3272_, lean_object* v_heq_3273_, lean_object* v_i_3274_, lean_object* v_entries_3275_){
_start:
{
size_t v_depth_boxed_3276_; lean_object* v_res_3277_; 
v_depth_boxed_3276_ = lean_unbox_usize(v_depth_3270_);
lean_dec(v_depth_3270_);
v_res_3277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3269_, v_depth_boxed_3276_, v_keys_3271_, v_vals_3272_, v_heq_3273_, v_i_3274_, v_entries_3275_);
lean_dec_ref(v_vals_3272_);
lean_dec_ref(v_keys_3271_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3279_, v_x_3280_, v_x_3281_, v_x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3284_, lean_object* v_as_3285_, size_t v_i_3286_, size_t v_stop_3287_){
_start:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_usize_dec_eq(v_i_3286_, v_stop_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = lean_array_uget_borrowed(v_as_3285_, v_i_3286_);
v___x_3290_ = l_Lean_instBEqFVarId_beq(v_a_3284_, v___x_3289_);
if (v___x_3290_ == 0)
{
size_t v___x_3291_; size_t v___x_3292_; 
v___x_3291_ = ((size_t)1ULL);
v___x_3292_ = lean_usize_add(v_i_3286_, v___x_3291_);
v_i_3286_ = v___x_3292_;
goto _start;
}
else
{
return v___x_3290_;
}
}
else
{
uint8_t v___x_3294_; 
v___x_3294_ = 0;
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3295_, lean_object* v_as_3296_, lean_object* v_i_3297_, lean_object* v_stop_3298_){
_start:
{
size_t v_i_boxed_3299_; size_t v_stop_boxed_3300_; uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_i_boxed_3299_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_stop_boxed_3300_ = lean_unbox_usize(v_stop_3298_);
lean_dec(v_stop_3298_);
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3295_, v_as_3296_, v_i_boxed_3299_, v_stop_boxed_3300_);
lean_dec_ref(v_as_3296_);
lean_dec(v_a_3295_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = lean_array_get_size(v_as_3303_);
v___x_3307_ = lean_nat_dec_lt(v___x_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
return v___x_3307_;
}
else
{
size_t v___x_3308_; size_t v___x_3309_; uint8_t v___x_3310_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3306_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3304_, v_as_3303_, v___x_3308_, v___x_3309_);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3311_, lean_object* v_a_3312_){
_start:
{
uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_res_3313_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_as_3311_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3315_, v___y_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v_res_3320_; lean_object* v_r_3321_; 
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec(v_snd_3318_);
v_r_3321_ = lean_box(v_res_3320_);
return v_r_3321_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3322_){
_start:
{
uint8_t v___x_3323_; 
v___x_3323_ = 0;
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3324_);
lean_dec(v_x_3324_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_unsigned_to_nat(16u);
v___x_3330_ = lean_mk_array(v___x_3329_, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3331_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3334_, size_t v_sz_3335_, size_t v_i_3336_, lean_object* v_b_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_lt(v_i_3336_, v_sz_3335_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_b_3337_);
return v___x_3341_;
}
else
{
lean_object* v_snd_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3474_; 
v_snd_3342_ = lean_ctor_get(v_b_3337_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_b_3337_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v_b_3337_, 0);
lean_dec(v_unused_3475_);
v___x_3344_ = v_b_3337_;
v_isShared_3345_ = v_isSharedCheck_3474_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3342_);
lean_dec(v_b_3337_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3474_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v_a_3348_; lean_object* v_a_3355_; 
v___x_3346_ = lean_box(0);
v_a_3355_ = lean_array_uget_borrowed(v_as_3334_, v_i_3336_);
if (lean_obj_tag(v_a_3355_) == 0)
{
v_a_3348_ = v_snd_3342_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3356_; uint8_t v_a_3358_; lean_object* v___f_3361_; lean_object* v___f_3362_; 
v_val_3356_ = lean_ctor_get(v_a_3355_, 0);
v___f_3361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3342_);
v___f_3362_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3362_, 0, v_snd_3342_);
if (lean_obj_tag(v_val_3356_) == 0)
{
lean_object* v_type_3363_; lean_object* v___x_3364_; uint8_t v_fst_3366_; lean_object* v_mctx_3367_; lean_object* v___y_3383_; lean_object* v_mctx_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_type_3363_ = lean_ctor_get(v_val_3356_, 3);
v___x_3364_ = lean_st_ref_get(v___y_3338_);
v_mctx_3388_ = lean_ctor_get(v___x_3364_, 0);
lean_inc_ref_n(v_mctx_3388_, 2);
lean_dec(v___x_3364_);
v___x_3389_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v_mctx_3388_);
v___x_3391_ = l_Lean_Expr_hasFVar(v_type_3363_);
if (v___x_3391_ == 0)
{
uint8_t v___x_3392_; 
v___x_3392_ = l_Lean_Expr_hasMVar(v_type_3363_);
if (v___x_3392_ == 0)
{
lean_dec_ref_known(v___x_3390_, 2);
lean_dec_ref(v___f_3362_);
v_fst_3366_ = v___x_3392_;
v_mctx_3367_ = v_mctx_3388_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3393_; 
lean_dec_ref(v_mctx_3388_);
lean_inc_ref(v_type_3363_);
v___x_3393_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3363_, v___x_3390_);
v___y_3383_ = v___x_3393_;
goto v___jp_3382_;
}
}
else
{
lean_object* v___x_3394_; 
lean_dec_ref(v_mctx_3388_);
lean_inc_ref(v_type_3363_);
v___x_3394_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3363_, v___x_3390_);
v___y_3383_ = v___x_3394_;
goto v___jp_3382_;
}
v___jp_3365_:
{
lean_object* v___x_3368_; lean_object* v_cache_3369_; lean_object* v_zetaDeltaFVarIds_3370_; lean_object* v_postponed_3371_; lean_object* v_diag_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
v___x_3368_ = lean_st_ref_take(v___y_3338_);
v_cache_3369_ = lean_ctor_get(v___x_3368_, 1);
v_zetaDeltaFVarIds_3370_ = lean_ctor_get(v___x_3368_, 2);
v_postponed_3371_ = lean_ctor_get(v___x_3368_, 3);
v_diag_3372_ = lean_ctor_get(v___x_3368_, 4);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3381_);
v___x_3374_ = v___x_3368_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_diag_3372_);
lean_inc(v_postponed_3371_);
lean_inc(v_zetaDeltaFVarIds_3370_);
lean_inc(v_cache_3369_);
lean_dec(v___x_3368_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v_mctx_3367_);
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_mctx_3367_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_cache_3369_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_zetaDeltaFVarIds_3370_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_postponed_3371_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_diag_3372_);
v___x_3377_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_st_ref_put(v___y_3338_, v___x_3377_);
v_a_3358_ = v_fst_3366_;
goto v___jp_3357_;
}
}
}
v___jp_3382_:
{
lean_object* v_snd_3384_; lean_object* v_fst_3385_; lean_object* v_mctx_3386_; uint8_t v___x_3387_; 
v_snd_3384_ = lean_ctor_get(v___y_3383_, 1);
lean_inc(v_snd_3384_);
v_fst_3385_ = lean_ctor_get(v___y_3383_, 0);
lean_inc(v_fst_3385_);
lean_dec_ref(v___y_3383_);
v_mctx_3386_ = lean_ctor_get(v_snd_3384_, 1);
lean_inc_ref(v_mctx_3386_);
lean_dec(v_snd_3384_);
v___x_3387_ = lean_unbox(v_fst_3385_);
lean_dec(v_fst_3385_);
v_fst_3366_ = v___x_3387_;
v_mctx_3367_ = v_mctx_3386_;
goto v___jp_3365_;
}
}
else
{
uint8_t v_nondep_3395_; 
v_nondep_3395_ = lean_ctor_get_uint8(v_val_3356_, sizeof(void*)*5);
if (v_nondep_3395_ == 0)
{
lean_object* v_type_3396_; lean_object* v_value_3397_; lean_object* v___x_3398_; uint8_t v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___y_3418_; lean_object* v_snd_3423_; lean_object* v___y_3429_; lean_object* v_mctx_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
v_type_3396_ = lean_ctor_get(v_val_3356_, 3);
v_value_3397_ = lean_ctor_get(v_val_3356_, 4);
v___x_3398_ = lean_st_ref_get(v___y_3338_);
v_mctx_3435_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_ref(v_mctx_3435_);
lean_dec(v___x_3398_);
v___x_3436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_mctx_3435_);
v___x_3438_ = l_Lean_Expr_hasFVar(v_type_3396_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = l_Lean_Expr_hasMVar(v_type_3396_);
if (v___x_3439_ == 0)
{
v_snd_3423_ = v___x_3437_;
goto v___jp_3422_;
}
else
{
lean_object* v___x_3440_; 
lean_inc_ref(v_type_3396_);
lean_inc_ref(v___f_3362_);
v___x_3440_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3396_, v___x_3437_);
v___y_3429_ = v___x_3440_;
goto v___jp_3428_;
}
}
else
{
lean_object* v___x_3441_; 
lean_inc_ref(v_type_3396_);
lean_inc_ref(v___f_3362_);
v___x_3441_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3396_, v___x_3437_);
v___y_3429_ = v___x_3441_;
goto v___jp_3428_;
}
v___jp_3399_:
{
lean_object* v_mctx_3402_; lean_object* v___x_3403_; lean_object* v_cache_3404_; lean_object* v_zetaDeltaFVarIds_3405_; lean_object* v_postponed_3406_; lean_object* v_diag_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3415_; 
v_mctx_3402_ = lean_ctor_get(v_snd_3401_, 1);
lean_inc_ref(v_mctx_3402_);
lean_dec_ref(v_snd_3401_);
v___x_3403_ = lean_st_ref_take(v___y_3338_);
v_cache_3404_ = lean_ctor_get(v___x_3403_, 1);
v_zetaDeltaFVarIds_3405_ = lean_ctor_get(v___x_3403_, 2);
v_postponed_3406_ = lean_ctor_get(v___x_3403_, 3);
v_diag_3407_ = lean_ctor_get(v___x_3403_, 4);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3403_, 0);
lean_dec(v_unused_3416_);
v___x_3409_ = v___x_3403_;
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_diag_3407_);
lean_inc(v_postponed_3406_);
lean_inc(v_zetaDeltaFVarIds_3405_);
lean_inc(v_cache_3404_);
lean_dec(v___x_3403_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_mctx_3402_);
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_mctx_3402_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_cache_3404_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_zetaDeltaFVarIds_3405_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_postponed_3406_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_diag_3407_);
v___x_3412_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_st_ref_put(v___y_3338_, v___x_3412_);
v_a_3358_ = v_fst_3400_;
goto v___jp_3357_;
}
}
}
v___jp_3417_:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; uint8_t v___x_3421_; 
v_fst_3419_ = lean_ctor_get(v___y_3418_, 0);
lean_inc(v_fst_3419_);
v_snd_3420_ = lean_ctor_get(v___y_3418_, 1);
lean_inc(v_snd_3420_);
lean_dec_ref(v___y_3418_);
v___x_3421_ = lean_unbox(v_fst_3419_);
lean_dec(v_fst_3419_);
v_fst_3400_ = v___x_3421_;
v_snd_3401_ = v_snd_3420_;
goto v___jp_3399_;
}
v___jp_3422_:
{
uint8_t v___x_3424_; 
v___x_3424_ = l_Lean_Expr_hasFVar(v_value_3397_);
if (v___x_3424_ == 0)
{
uint8_t v___x_3425_; 
v___x_3425_ = l_Lean_Expr_hasMVar(v_value_3397_);
if (v___x_3425_ == 0)
{
lean_dec_ref(v___f_3362_);
v_fst_3400_ = v___x_3425_;
v_snd_3401_ = v_snd_3423_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3426_; 
lean_inc_ref(v_value_3397_);
v___x_3426_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_value_3397_, v_snd_3423_);
v___y_3418_ = v___x_3426_;
goto v___jp_3417_;
}
}
else
{
lean_object* v___x_3427_; 
lean_inc_ref(v_value_3397_);
v___x_3427_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_value_3397_, v_snd_3423_);
v___y_3418_ = v___x_3427_;
goto v___jp_3417_;
}
}
v___jp_3428_:
{
lean_object* v_fst_3430_; uint8_t v___x_3431_; 
v_fst_3430_ = lean_ctor_get(v___y_3429_, 0);
v___x_3431_ = lean_unbox(v_fst_3430_);
if (v___x_3431_ == 0)
{
lean_object* v_snd_3432_; 
v_snd_3432_ = lean_ctor_get(v___y_3429_, 1);
lean_inc(v_snd_3432_);
lean_dec_ref(v___y_3429_);
v_snd_3423_ = v_snd_3432_;
goto v___jp_3422_;
}
else
{
lean_object* v_snd_3433_; uint8_t v___x_3434_; 
lean_inc(v_fst_3430_);
lean_dec_ref(v___f_3362_);
v_snd_3433_ = lean_ctor_get(v___y_3429_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v___y_3429_);
v___x_3434_ = lean_unbox(v_fst_3430_);
lean_dec(v_fst_3430_);
v_fst_3400_ = v___x_3434_;
v_snd_3401_ = v_snd_3433_;
goto v___jp_3399_;
}
}
}
else
{
lean_object* v_type_3442_; lean_object* v___x_3443_; uint8_t v_fst_3445_; lean_object* v_mctx_3446_; lean_object* v___y_3462_; lean_object* v_mctx_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v_type_3442_ = lean_ctor_get(v_val_3356_, 3);
v___x_3443_ = lean_st_ref_get(v___y_3338_);
v_mctx_3467_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_ref_n(v_mctx_3467_, 2);
lean_dec(v___x_3443_);
v___x_3468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v_mctx_3467_);
v___x_3470_ = l_Lean_Expr_hasFVar(v_type_3442_);
if (v___x_3470_ == 0)
{
uint8_t v___x_3471_; 
v___x_3471_ = l_Lean_Expr_hasMVar(v_type_3442_);
if (v___x_3471_ == 0)
{
lean_dec_ref_known(v___x_3469_, 2);
lean_dec_ref(v___f_3362_);
v_fst_3445_ = v___x_3471_;
v_mctx_3446_ = v_mctx_3467_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3472_; 
lean_dec_ref(v_mctx_3467_);
lean_inc_ref(v_type_3442_);
v___x_3472_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3442_, v___x_3469_);
v___y_3462_ = v___x_3472_;
goto v___jp_3461_;
}
}
else
{
lean_object* v___x_3473_; 
lean_dec_ref(v_mctx_3467_);
lean_inc_ref(v_type_3442_);
v___x_3473_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3362_, v___f_3361_, v_type_3442_, v___x_3469_);
v___y_3462_ = v___x_3473_;
goto v___jp_3461_;
}
v___jp_3444_:
{
lean_object* v___x_3447_; lean_object* v_cache_3448_; lean_object* v_zetaDeltaFVarIds_3449_; lean_object* v_postponed_3450_; lean_object* v_diag_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3459_; 
v___x_3447_ = lean_st_ref_take(v___y_3338_);
v_cache_3448_ = lean_ctor_get(v___x_3447_, 1);
v_zetaDeltaFVarIds_3449_ = lean_ctor_get(v___x_3447_, 2);
v_postponed_3450_ = lean_ctor_get(v___x_3447_, 3);
v_diag_3451_ = lean_ctor_get(v___x_3447_, 4);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3447_, 0);
lean_dec(v_unused_3460_);
v___x_3453_ = v___x_3447_;
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_diag_3451_);
lean_inc(v_postponed_3450_);
lean_inc(v_zetaDeltaFVarIds_3449_);
lean_inc(v_cache_3448_);
lean_dec(v___x_3447_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v_mctx_3446_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_mctx_3446_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_cache_3448_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_zetaDeltaFVarIds_3449_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_postponed_3450_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_diag_3451_);
v___x_3456_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_st_ref_put(v___y_3338_, v___x_3456_);
v_a_3358_ = v_fst_3445_;
goto v___jp_3357_;
}
}
}
v___jp_3461_:
{
lean_object* v_snd_3463_; lean_object* v_fst_3464_; lean_object* v_mctx_3465_; uint8_t v___x_3466_; 
v_snd_3463_ = lean_ctor_get(v___y_3462_, 1);
lean_inc(v_snd_3463_);
v_fst_3464_ = lean_ctor_get(v___y_3462_, 0);
lean_inc(v_fst_3464_);
lean_dec_ref(v___y_3462_);
v_mctx_3465_ = lean_ctor_get(v_snd_3463_, 1);
lean_inc_ref(v_mctx_3465_);
lean_dec(v_snd_3463_);
v___x_3466_ = lean_unbox(v_fst_3464_);
lean_dec(v_fst_3464_);
v_fst_3445_ = v___x_3466_;
v_mctx_3446_ = v_mctx_3465_;
goto v___jp_3444_;
}
}
}
v___jp_3357_:
{
if (v_a_3358_ == 0)
{
v_a_3348_ = v_snd_3342_;
goto v___jp_3347_;
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = l_Lean_LocalDecl_fvarId(v_val_3356_);
v___x_3360_ = lean_array_push(v_snd_3342_, v___x_3359_);
v_a_3348_ = v___x_3360_;
goto v___jp_3347_;
}
}
}
v___jp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v_a_3348_);
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3350_ = v___x_3344_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3348_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
size_t v___x_3351_; size_t v___x_3352_; 
v___x_3351_ = ((size_t)1ULL);
v___x_3352_ = lean_usize_add(v_i_3336_, v___x_3351_);
v_i_3336_ = v___x_3352_;
v_b_3337_ = v___x_3350_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3476_, lean_object* v_sz_3477_, lean_object* v_i_3478_, lean_object* v_b_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
size_t v_sz_boxed_3482_; size_t v_i_boxed_3483_; lean_object* v_res_3484_; 
v_sz_boxed_3482_ = lean_unbox_usize(v_sz_3477_);
lean_dec(v_sz_3477_);
v_i_boxed_3483_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3476_, v_sz_boxed_3482_, v_i_boxed_3483_, v_b_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v_as_3476_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3485_, size_t v_sz_3486_, size_t v_i_3487_, lean_object* v_b_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3487_, v_sz_3486_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_b_3488_);
return v___x_3495_;
}
else
{
lean_object* v_snd_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3628_; 
v_snd_3496_ = lean_ctor_get(v_b_3488_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_b_3488_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v_b_3488_, 0);
lean_dec(v_unused_3629_);
v___x_3498_ = v_b_3488_;
v_isShared_3499_ = v_isSharedCheck_3628_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_snd_3496_);
lean_dec(v_b_3488_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3628_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v_a_3502_; lean_object* v_a_3509_; 
v___x_3500_ = lean_box(0);
v_a_3509_ = lean_array_uget_borrowed(v_as_3485_, v_i_3487_);
if (lean_obj_tag(v_a_3509_) == 0)
{
v_a_3502_ = v_snd_3496_;
goto v___jp_3501_;
}
else
{
lean_object* v_val_3510_; uint8_t v_a_3512_; lean_object* v___f_3515_; lean_object* v___f_3516_; 
v_val_3510_ = lean_ctor_get(v_a_3509_, 0);
v___f_3515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3496_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3516_, 0, v_snd_3496_);
if (lean_obj_tag(v_val_3510_) == 0)
{
lean_object* v_type_3517_; lean_object* v___x_3518_; uint8_t v_fst_3520_; lean_object* v_mctx_3521_; lean_object* v___y_3537_; lean_object* v_mctx_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_type_3517_ = lean_ctor_get(v_val_3510_, 3);
v___x_3518_ = lean_st_ref_get(v___y_3490_);
v_mctx_3542_ = lean_ctor_get(v___x_3518_, 0);
lean_inc_ref_n(v_mctx_3542_, 2);
lean_dec(v___x_3518_);
v___x_3543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v_mctx_3542_);
v___x_3545_ = l_Lean_Expr_hasFVar(v_type_3517_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; 
v___x_3546_ = l_Lean_Expr_hasMVar(v_type_3517_);
if (v___x_3546_ == 0)
{
lean_dec_ref_known(v___x_3544_, 2);
lean_dec_ref(v___f_3516_);
v_fst_3520_ = v___x_3546_;
v_mctx_3521_ = v_mctx_3542_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3547_; 
lean_dec_ref(v_mctx_3542_);
lean_inc_ref(v_type_3517_);
v___x_3547_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3517_, v___x_3544_);
v___y_3537_ = v___x_3547_;
goto v___jp_3536_;
}
}
else
{
lean_object* v___x_3548_; 
lean_dec_ref(v_mctx_3542_);
lean_inc_ref(v_type_3517_);
v___x_3548_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3517_, v___x_3544_);
v___y_3537_ = v___x_3548_;
goto v___jp_3536_;
}
v___jp_3519_:
{
lean_object* v___x_3522_; lean_object* v_cache_3523_; lean_object* v_zetaDeltaFVarIds_3524_; lean_object* v_postponed_3525_; lean_object* v_diag_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v___x_3522_ = lean_st_ref_take(v___y_3490_);
v_cache_3523_ = lean_ctor_get(v___x_3522_, 1);
v_zetaDeltaFVarIds_3524_ = lean_ctor_get(v___x_3522_, 2);
v_postponed_3525_ = lean_ctor_get(v___x_3522_, 3);
v_diag_3526_ = lean_ctor_get(v___x_3522_, 4);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v___x_3522_, 0);
lean_dec(v_unused_3535_);
v___x_3528_ = v___x_3522_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_diag_3526_);
lean_inc(v_postponed_3525_);
lean_inc(v_zetaDeltaFVarIds_3524_);
lean_inc(v_cache_3523_);
lean_dec(v___x_3522_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_mctx_3521_);
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_mctx_3521_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_cache_3523_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_zetaDeltaFVarIds_3524_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_postponed_3525_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_diag_3526_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_st_ref_put(v___y_3490_, v___x_3531_);
v_a_3512_ = v_fst_3520_;
goto v___jp_3511_;
}
}
}
v___jp_3536_:
{
lean_object* v_snd_3538_; lean_object* v_fst_3539_; lean_object* v_mctx_3540_; uint8_t v___x_3541_; 
v_snd_3538_ = lean_ctor_get(v___y_3537_, 1);
lean_inc(v_snd_3538_);
v_fst_3539_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_fst_3539_);
lean_dec_ref(v___y_3537_);
v_mctx_3540_ = lean_ctor_get(v_snd_3538_, 1);
lean_inc_ref(v_mctx_3540_);
lean_dec(v_snd_3538_);
v___x_3541_ = lean_unbox(v_fst_3539_);
lean_dec(v_fst_3539_);
v_fst_3520_ = v___x_3541_;
v_mctx_3521_ = v_mctx_3540_;
goto v___jp_3519_;
}
}
else
{
uint8_t v_nondep_3549_; 
v_nondep_3549_ = lean_ctor_get_uint8(v_val_3510_, sizeof(void*)*5);
if (v_nondep_3549_ == 0)
{
lean_object* v_type_3550_; lean_object* v_value_3551_; lean_object* v___x_3552_; uint8_t v_fst_3554_; lean_object* v_snd_3555_; lean_object* v___y_3572_; lean_object* v_snd_3577_; lean_object* v___y_3583_; lean_object* v_mctx_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v_type_3550_ = lean_ctor_get(v_val_3510_, 3);
v_value_3551_ = lean_ctor_get(v_val_3510_, 4);
v___x_3552_ = lean_st_ref_get(v___y_3490_);
v_mctx_3589_ = lean_ctor_get(v___x_3552_, 0);
lean_inc_ref(v_mctx_3589_);
lean_dec(v___x_3552_);
v___x_3590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v_mctx_3589_);
v___x_3592_ = l_Lean_Expr_hasFVar(v_type_3550_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = l_Lean_Expr_hasMVar(v_type_3550_);
if (v___x_3593_ == 0)
{
v_snd_3577_ = v___x_3591_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3594_; 
lean_inc_ref(v_type_3550_);
lean_inc_ref(v___f_3516_);
v___x_3594_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3550_, v___x_3591_);
v___y_3583_ = v___x_3594_;
goto v___jp_3582_;
}
}
else
{
lean_object* v___x_3595_; 
lean_inc_ref(v_type_3550_);
lean_inc_ref(v___f_3516_);
v___x_3595_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3550_, v___x_3591_);
v___y_3583_ = v___x_3595_;
goto v___jp_3582_;
}
v___jp_3553_:
{
lean_object* v_mctx_3556_; lean_object* v___x_3557_; lean_object* v_cache_3558_; lean_object* v_zetaDeltaFVarIds_3559_; lean_object* v_postponed_3560_; lean_object* v_diag_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3569_; 
v_mctx_3556_ = lean_ctor_get(v_snd_3555_, 1);
lean_inc_ref(v_mctx_3556_);
lean_dec_ref(v_snd_3555_);
v___x_3557_ = lean_st_ref_take(v___y_3490_);
v_cache_3558_ = lean_ctor_get(v___x_3557_, 1);
v_zetaDeltaFVarIds_3559_ = lean_ctor_get(v___x_3557_, 2);
v_postponed_3560_ = lean_ctor_get(v___x_3557_, 3);
v_diag_3561_ = lean_ctor_get(v___x_3557_, 4);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v___x_3557_, 0);
lean_dec(v_unused_3570_);
v___x_3563_ = v___x_3557_;
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_diag_3561_);
lean_inc(v_postponed_3560_);
lean_inc(v_zetaDeltaFVarIds_3559_);
lean_inc(v_cache_3558_);
lean_dec(v___x_3557_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v_mctx_3556_);
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_mctx_3556_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_cache_3558_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_zetaDeltaFVarIds_3559_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_postponed_3560_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_diag_3561_);
v___x_3566_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_st_ref_put(v___y_3490_, v___x_3566_);
v_a_3512_ = v_fst_3554_;
goto v___jp_3511_;
}
}
}
v___jp_3571_:
{
lean_object* v_fst_3573_; lean_object* v_snd_3574_; uint8_t v___x_3575_; 
v_fst_3573_ = lean_ctor_get(v___y_3572_, 0);
lean_inc(v_fst_3573_);
v_snd_3574_ = lean_ctor_get(v___y_3572_, 1);
lean_inc(v_snd_3574_);
lean_dec_ref(v___y_3572_);
v___x_3575_ = lean_unbox(v_fst_3573_);
lean_dec(v_fst_3573_);
v_fst_3554_ = v___x_3575_;
v_snd_3555_ = v_snd_3574_;
goto v___jp_3553_;
}
v___jp_3576_:
{
uint8_t v___x_3578_; 
v___x_3578_ = l_Lean_Expr_hasFVar(v_value_3551_);
if (v___x_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_Expr_hasMVar(v_value_3551_);
if (v___x_3579_ == 0)
{
lean_dec_ref(v___f_3516_);
v_fst_3554_ = v___x_3579_;
v_snd_3555_ = v_snd_3577_;
goto v___jp_3553_;
}
else
{
lean_object* v___x_3580_; 
lean_inc_ref(v_value_3551_);
v___x_3580_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_value_3551_, v_snd_3577_);
v___y_3572_ = v___x_3580_;
goto v___jp_3571_;
}
}
else
{
lean_object* v___x_3581_; 
lean_inc_ref(v_value_3551_);
v___x_3581_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_value_3551_, v_snd_3577_);
v___y_3572_ = v___x_3581_;
goto v___jp_3571_;
}
}
v___jp_3582_:
{
lean_object* v_fst_3584_; uint8_t v___x_3585_; 
v_fst_3584_ = lean_ctor_get(v___y_3583_, 0);
v___x_3585_ = lean_unbox(v_fst_3584_);
if (v___x_3585_ == 0)
{
lean_object* v_snd_3586_; 
v_snd_3586_ = lean_ctor_get(v___y_3583_, 1);
lean_inc(v_snd_3586_);
lean_dec_ref(v___y_3583_);
v_snd_3577_ = v_snd_3586_;
goto v___jp_3576_;
}
else
{
lean_object* v_snd_3587_; uint8_t v___x_3588_; 
lean_inc(v_fst_3584_);
lean_dec_ref(v___f_3516_);
v_snd_3587_ = lean_ctor_get(v___y_3583_, 1);
lean_inc(v_snd_3587_);
lean_dec_ref(v___y_3583_);
v___x_3588_ = lean_unbox(v_fst_3584_);
lean_dec(v_fst_3584_);
v_fst_3554_ = v___x_3588_;
v_snd_3555_ = v_snd_3587_;
goto v___jp_3553_;
}
}
}
else
{
lean_object* v_type_3596_; lean_object* v___x_3597_; uint8_t v_fst_3599_; lean_object* v_mctx_3600_; lean_object* v___y_3616_; lean_object* v_mctx_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v_type_3596_ = lean_ctor_get(v_val_3510_, 3);
v___x_3597_ = lean_st_ref_get(v___y_3490_);
v_mctx_3621_ = lean_ctor_get(v___x_3597_, 0);
lean_inc_ref_n(v_mctx_3621_, 2);
lean_dec(v___x_3597_);
v___x_3622_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v_mctx_3621_);
v___x_3624_ = l_Lean_Expr_hasFVar(v_type_3596_);
if (v___x_3624_ == 0)
{
uint8_t v___x_3625_; 
v___x_3625_ = l_Lean_Expr_hasMVar(v_type_3596_);
if (v___x_3625_ == 0)
{
lean_dec_ref_known(v___x_3623_, 2);
lean_dec_ref(v___f_3516_);
v_fst_3599_ = v___x_3625_;
v_mctx_3600_ = v_mctx_3621_;
goto v___jp_3598_;
}
else
{
lean_object* v___x_3626_; 
lean_dec_ref(v_mctx_3621_);
lean_inc_ref(v_type_3596_);
v___x_3626_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3596_, v___x_3623_);
v___y_3616_ = v___x_3626_;
goto v___jp_3615_;
}
}
else
{
lean_object* v___x_3627_; 
lean_dec_ref(v_mctx_3621_);
lean_inc_ref(v_type_3596_);
v___x_3627_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3516_, v___f_3515_, v_type_3596_, v___x_3623_);
v___y_3616_ = v___x_3627_;
goto v___jp_3615_;
}
v___jp_3598_:
{
lean_object* v___x_3601_; lean_object* v_cache_3602_; lean_object* v_zetaDeltaFVarIds_3603_; lean_object* v_postponed_3604_; lean_object* v_diag_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3613_; 
v___x_3601_ = lean_st_ref_take(v___y_3490_);
v_cache_3602_ = lean_ctor_get(v___x_3601_, 1);
v_zetaDeltaFVarIds_3603_ = lean_ctor_get(v___x_3601_, 2);
v_postponed_3604_ = lean_ctor_get(v___x_3601_, 3);
v_diag_3605_ = lean_ctor_get(v___x_3601_, 4);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3601_, 0);
lean_dec(v_unused_3614_);
v___x_3607_ = v___x_3601_;
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_diag_3605_);
lean_inc(v_postponed_3604_);
lean_inc(v_zetaDeltaFVarIds_3603_);
lean_inc(v_cache_3602_);
lean_dec(v___x_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v_mctx_3600_);
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_mctx_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_cache_3602_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_zetaDeltaFVarIds_3603_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_postponed_3604_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_diag_3605_);
v___x_3610_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_st_ref_put(v___y_3490_, v___x_3610_);
v_a_3512_ = v_fst_3599_;
goto v___jp_3511_;
}
}
}
v___jp_3615_:
{
lean_object* v_snd_3617_; lean_object* v_fst_3618_; lean_object* v_mctx_3619_; uint8_t v___x_3620_; 
v_snd_3617_ = lean_ctor_get(v___y_3616_, 1);
lean_inc(v_snd_3617_);
v_fst_3618_ = lean_ctor_get(v___y_3616_, 0);
lean_inc(v_fst_3618_);
lean_dec_ref(v___y_3616_);
v_mctx_3619_ = lean_ctor_get(v_snd_3617_, 1);
lean_inc_ref(v_mctx_3619_);
lean_dec(v_snd_3617_);
v___x_3620_ = lean_unbox(v_fst_3618_);
lean_dec(v_fst_3618_);
v_fst_3599_ = v___x_3620_;
v_mctx_3600_ = v_mctx_3619_;
goto v___jp_3598_;
}
}
}
v___jp_3511_:
{
if (v_a_3512_ == 0)
{
v_a_3502_ = v_snd_3496_;
goto v___jp_3501_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = l_Lean_LocalDecl_fvarId(v_val_3510_);
v___x_3514_ = lean_array_push(v_snd_3496_, v___x_3513_);
v_a_3502_ = v___x_3514_;
goto v___jp_3501_;
}
}
}
v___jp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v_a_3502_);
lean_ctor_set(v___x_3498_, 0, v___x_3500_);
v___x_3504_ = v___x_3498_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_a_3502_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_add(v_i_3487_, v___x_3505_);
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3485_, v_sz_3486_, v___x_3506_, v___x_3504_, v___y_3490_);
return v___x_3507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3630_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v_as_3630_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3642_, lean_object* v_n_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
if (lean_obj_tag(v_n_3643_) == 0)
{
lean_object* v_cs_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; size_t v_sz_3653_; size_t v___x_3654_; lean_object* v___x_3655_; 
v_cs_3650_ = lean_ctor_get(v_n_3643_, 0);
v___x_3651_ = lean_box(0);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v_b_3644_);
v_sz_3653_ = lean_array_size(v_cs_3650_);
v___x_3654_ = ((size_t)0ULL);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3642_, v_cs_3650_, v_sz_3653_, v___x_3654_, v___x_3652_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3670_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v_fst_3660_; 
v_fst_3660_ = lean_ctor_get(v_a_3656_, 0);
if (lean_obj_tag(v_fst_3660_) == 0)
{
lean_object* v_snd_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
v_snd_3661_ = lean_ctor_get(v_a_3656_, 1);
lean_inc(v_snd_3661_);
lean_dec(v_a_3656_);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_snd_3661_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3662_);
v___x_3664_ = v___x_3658_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
else
{
lean_object* v_val_3666_; lean_object* v___x_3668_; 
lean_inc_ref(v_fst_3660_);
lean_dec(v_a_3656_);
v_val_3666_ = lean_ctor_get(v_fst_3660_, 0);
lean_inc(v_val_3666_);
lean_dec_ref_known(v_fst_3660_, 1);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v_val_3666_);
v___x_3668_ = v___x_3658_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_val_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_a_3671_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3655_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3655_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_vs_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; size_t v_sz_3682_; size_t v___x_3683_; lean_object* v___x_3684_; 
v_vs_3679_ = lean_ctor_get(v_n_3643_, 0);
v___x_3680_ = lean_box(0);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v_b_3644_);
v_sz_3682_ = lean_array_size(v_vs_3679_);
v___x_3683_ = ((size_t)0ULL);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3679_, v_sz_3682_, v___x_3683_, v___x_3681_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3699_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_fst_3689_; 
v_fst_3689_ = lean_ctor_get(v_a_3685_, 0);
if (lean_obj_tag(v_fst_3689_) == 0)
{
lean_object* v_snd_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v_snd_3690_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3690_);
lean_dec(v_a_3685_);
v___x_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_snd_3690_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3691_);
v___x_3693_ = v___x_3687_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
else
{
lean_object* v_val_3695_; lean_object* v___x_3697_; 
lean_inc_ref(v_fst_3689_);
lean_dec(v_a_3685_);
v_val_3695_ = lean_ctor_get(v_fst_3689_, 0);
lean_inc(v_val_3695_);
lean_dec_ref_known(v_fst_3689_, 1);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v_val_3695_);
v___x_3697_ = v___x_3687_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_val_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_a_3700_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3684_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3684_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3708_, lean_object* v_as_3709_, size_t v_sz_3710_, size_t v_i_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_usize_dec_lt(v_i_3711_, v_sz_3710_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v_b_3712_);
return v___x_3719_;
}
else
{
lean_object* v_snd_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3754_; 
v_snd_3720_ = lean_ctor_get(v_b_3712_, 1);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_b_3712_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; 
v_unused_3755_ = lean_ctor_get(v_b_3712_, 0);
lean_dec(v_unused_3755_);
v___x_3722_ = v_b_3712_;
v_isShared_3723_ = v_isSharedCheck_3754_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_snd_3720_);
lean_dec(v_b_3712_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3754_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3726_; 
v___x_3724_ = lean_box(0);
v_a_3725_ = lean_array_uget_borrowed(v_as_3709_, v_i_3711_);
lean_inc(v_snd_3720_);
v___x_3726_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3708_, v_a_3725_, v_snd_3720_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3745_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3745_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3745_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
if (lean_obj_tag(v_a_3727_) == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_a_3727_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3731_);
v___x_3733_ = v___x_3722_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_snd_3720_);
v___x_3733_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3733_);
v___x_3735_ = v___x_3729_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; 
lean_del_object(v___x_3729_);
lean_dec(v_snd_3720_);
v_a_3738_ = lean_ctor_get(v_a_3727_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v_a_3727_, 1);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v_a_3738_);
lean_ctor_set(v___x_3722_, 0, v___x_3724_);
v___x_3740_ = v___x_3722_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_a_3738_);
v___x_3740_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
size_t v___x_3741_; size_t v___x_3742_; 
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3711_, v___x_3741_);
v_i_3711_ = v___x_3742_;
v_b_3712_ = v___x_3740_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_del_object(v___x_3722_);
lean_dec(v_snd_3720_);
v_a_3746_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3726_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3726_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3756_, lean_object* v_as_3757_, lean_object* v_sz_3758_, lean_object* v_i_3759_, lean_object* v_b_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
size_t v_sz_boxed_3766_; size_t v_i_boxed_3767_; lean_object* v_res_3768_; 
v_sz_boxed_3766_ = lean_unbox_usize(v_sz_3758_);
lean_dec(v_sz_3758_);
v_i_boxed_3767_ = lean_unbox_usize(v_i_3759_);
lean_dec(v_i_3759_);
v_res_3768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3756_, v_as_3757_, v_sz_boxed_3766_, v_i_boxed_3767_, v_b_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec_ref(v_as_3757_);
lean_dec_ref(v_init_3756_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3769_, lean_object* v_n_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3769_, v_n_3770_, v_b_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec_ref(v_n_3770_);
lean_dec_ref(v_init_3769_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3778_, size_t v_sz_3779_, size_t v_i_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3780_, v_sz_3779_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_b_3781_);
return v___x_3785_;
}
else
{
lean_object* v_snd_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3918_; 
v_snd_3786_ = lean_ctor_get(v_b_3781_, 1);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_b_3781_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v_b_3781_, 0);
lean_dec(v_unused_3919_);
v___x_3788_ = v_b_3781_;
v_isShared_3789_ = v_isSharedCheck_3918_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_snd_3786_);
lean_dec(v_b_3781_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3918_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v_a_3792_; lean_object* v_a_3799_; 
v___x_3790_ = lean_box(0);
v_a_3799_ = lean_array_uget_borrowed(v_as_3778_, v_i_3780_);
if (lean_obj_tag(v_a_3799_) == 0)
{
v_a_3792_ = v_snd_3786_;
goto v___jp_3791_;
}
else
{
lean_object* v_val_3800_; uint8_t v_a_3802_; lean_object* v___f_3805_; lean_object* v___f_3806_; 
v_val_3800_ = lean_ctor_get(v_a_3799_, 0);
v___f_3805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3786_);
v___f_3806_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3806_, 0, v_snd_3786_);
if (lean_obj_tag(v_val_3800_) == 0)
{
lean_object* v_type_3807_; lean_object* v___x_3808_; uint8_t v_fst_3810_; lean_object* v_mctx_3811_; lean_object* v___y_3827_; lean_object* v_mctx_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_type_3807_ = lean_ctor_get(v_val_3800_, 3);
v___x_3808_ = lean_st_ref_get(v___y_3782_);
v_mctx_3832_ = lean_ctor_get(v___x_3808_, 0);
lean_inc_ref_n(v_mctx_3832_, 2);
lean_dec(v___x_3808_);
v___x_3833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v_mctx_3832_);
v___x_3835_ = l_Lean_Expr_hasFVar(v_type_3807_);
if (v___x_3835_ == 0)
{
uint8_t v___x_3836_; 
v___x_3836_ = l_Lean_Expr_hasMVar(v_type_3807_);
if (v___x_3836_ == 0)
{
lean_dec_ref_known(v___x_3834_, 2);
lean_dec_ref(v___f_3806_);
v_fst_3810_ = v___x_3836_;
v_mctx_3811_ = v_mctx_3832_;
goto v___jp_3809_;
}
else
{
lean_object* v___x_3837_; 
lean_dec_ref(v_mctx_3832_);
lean_inc_ref(v_type_3807_);
v___x_3837_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3807_, v___x_3834_);
v___y_3827_ = v___x_3837_;
goto v___jp_3826_;
}
}
else
{
lean_object* v___x_3838_; 
lean_dec_ref(v_mctx_3832_);
lean_inc_ref(v_type_3807_);
v___x_3838_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3807_, v___x_3834_);
v___y_3827_ = v___x_3838_;
goto v___jp_3826_;
}
v___jp_3809_:
{
lean_object* v___x_3812_; lean_object* v_cache_3813_; lean_object* v_zetaDeltaFVarIds_3814_; lean_object* v_postponed_3815_; lean_object* v_diag_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
v___x_3812_ = lean_st_ref_take(v___y_3782_);
v_cache_3813_ = lean_ctor_get(v___x_3812_, 1);
v_zetaDeltaFVarIds_3814_ = lean_ctor_get(v___x_3812_, 2);
v_postponed_3815_ = lean_ctor_get(v___x_3812_, 3);
v_diag_3816_ = lean_ctor_get(v___x_3812_, 4);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; 
v_unused_3825_ = lean_ctor_get(v___x_3812_, 0);
lean_dec(v_unused_3825_);
v___x_3818_ = v___x_3812_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_diag_3816_);
lean_inc(v_postponed_3815_);
lean_inc(v_zetaDeltaFVarIds_3814_);
lean_inc(v_cache_3813_);
lean_dec(v___x_3812_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_mctx_3811_);
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_mctx_3811_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_cache_3813_);
lean_ctor_set(v_reuseFailAlloc_3823_, 2, v_zetaDeltaFVarIds_3814_);
lean_ctor_set(v_reuseFailAlloc_3823_, 3, v_postponed_3815_);
lean_ctor_set(v_reuseFailAlloc_3823_, 4, v_diag_3816_);
v___x_3821_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_st_ref_put(v___y_3782_, v___x_3821_);
v_a_3802_ = v_fst_3810_;
goto v___jp_3801_;
}
}
}
v___jp_3826_:
{
lean_object* v_snd_3828_; lean_object* v_fst_3829_; lean_object* v_mctx_3830_; uint8_t v___x_3831_; 
v_snd_3828_ = lean_ctor_get(v___y_3827_, 1);
lean_inc(v_snd_3828_);
v_fst_3829_ = lean_ctor_get(v___y_3827_, 0);
lean_inc(v_fst_3829_);
lean_dec_ref(v___y_3827_);
v_mctx_3830_ = lean_ctor_get(v_snd_3828_, 1);
lean_inc_ref(v_mctx_3830_);
lean_dec(v_snd_3828_);
v___x_3831_ = lean_unbox(v_fst_3829_);
lean_dec(v_fst_3829_);
v_fst_3810_ = v___x_3831_;
v_mctx_3811_ = v_mctx_3830_;
goto v___jp_3809_;
}
}
else
{
uint8_t v_nondep_3839_; 
v_nondep_3839_ = lean_ctor_get_uint8(v_val_3800_, sizeof(void*)*5);
if (v_nondep_3839_ == 0)
{
lean_object* v_type_3840_; lean_object* v_value_3841_; lean_object* v___x_3842_; uint8_t v_fst_3844_; lean_object* v_snd_3845_; lean_object* v___y_3862_; lean_object* v_snd_3867_; lean_object* v___y_3873_; lean_object* v_mctx_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v_type_3840_ = lean_ctor_get(v_val_3800_, 3);
v_value_3841_ = lean_ctor_get(v_val_3800_, 4);
v___x_3842_ = lean_st_ref_get(v___y_3782_);
v_mctx_3879_ = lean_ctor_get(v___x_3842_, 0);
lean_inc_ref(v_mctx_3879_);
lean_dec(v___x_3842_);
v___x_3880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
lean_ctor_set(v___x_3881_, 1, v_mctx_3879_);
v___x_3882_ = l_Lean_Expr_hasFVar(v_type_3840_);
if (v___x_3882_ == 0)
{
uint8_t v___x_3883_; 
v___x_3883_ = l_Lean_Expr_hasMVar(v_type_3840_);
if (v___x_3883_ == 0)
{
v_snd_3867_ = v___x_3881_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3884_; 
lean_inc_ref(v_type_3840_);
lean_inc_ref(v___f_3806_);
v___x_3884_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3840_, v___x_3881_);
v___y_3873_ = v___x_3884_;
goto v___jp_3872_;
}
}
else
{
lean_object* v___x_3885_; 
lean_inc_ref(v_type_3840_);
lean_inc_ref(v___f_3806_);
v___x_3885_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3840_, v___x_3881_);
v___y_3873_ = v___x_3885_;
goto v___jp_3872_;
}
v___jp_3843_:
{
lean_object* v_mctx_3846_; lean_object* v___x_3847_; lean_object* v_cache_3848_; lean_object* v_zetaDeltaFVarIds_3849_; lean_object* v_postponed_3850_; lean_object* v_diag_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3859_; 
v_mctx_3846_ = lean_ctor_get(v_snd_3845_, 1);
lean_inc_ref(v_mctx_3846_);
lean_dec_ref(v_snd_3845_);
v___x_3847_ = lean_st_ref_take(v___y_3782_);
v_cache_3848_ = lean_ctor_get(v___x_3847_, 1);
v_zetaDeltaFVarIds_3849_ = lean_ctor_get(v___x_3847_, 2);
v_postponed_3850_ = lean_ctor_get(v___x_3847_, 3);
v_diag_3851_ = lean_ctor_get(v___x_3847_, 4);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v___x_3847_, 0);
lean_dec(v_unused_3860_);
v___x_3853_ = v___x_3847_;
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_diag_3851_);
lean_inc(v_postponed_3850_);
lean_inc(v_zetaDeltaFVarIds_3849_);
lean_inc(v_cache_3848_);
lean_dec(v___x_3847_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v_mctx_3846_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_mctx_3846_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_cache_3848_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_zetaDeltaFVarIds_3849_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_postponed_3850_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_diag_3851_);
v___x_3856_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_st_ref_put(v___y_3782_, v___x_3856_);
v_a_3802_ = v_fst_3844_;
goto v___jp_3801_;
}
}
}
v___jp_3861_:
{
lean_object* v_fst_3863_; lean_object* v_snd_3864_; uint8_t v___x_3865_; 
v_fst_3863_ = lean_ctor_get(v___y_3862_, 0);
lean_inc(v_fst_3863_);
v_snd_3864_ = lean_ctor_get(v___y_3862_, 1);
lean_inc(v_snd_3864_);
lean_dec_ref(v___y_3862_);
v___x_3865_ = lean_unbox(v_fst_3863_);
lean_dec(v_fst_3863_);
v_fst_3844_ = v___x_3865_;
v_snd_3845_ = v_snd_3864_;
goto v___jp_3843_;
}
v___jp_3866_:
{
uint8_t v___x_3868_; 
v___x_3868_ = l_Lean_Expr_hasFVar(v_value_3841_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_Expr_hasMVar(v_value_3841_);
if (v___x_3869_ == 0)
{
lean_dec_ref(v___f_3806_);
v_fst_3844_ = v___x_3869_;
v_snd_3845_ = v_snd_3867_;
goto v___jp_3843_;
}
else
{
lean_object* v___x_3870_; 
lean_inc_ref(v_value_3841_);
v___x_3870_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_value_3841_, v_snd_3867_);
v___y_3862_ = v___x_3870_;
goto v___jp_3861_;
}
}
else
{
lean_object* v___x_3871_; 
lean_inc_ref(v_value_3841_);
v___x_3871_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_value_3841_, v_snd_3867_);
v___y_3862_ = v___x_3871_;
goto v___jp_3861_;
}
}
v___jp_3872_:
{
lean_object* v_fst_3874_; uint8_t v___x_3875_; 
v_fst_3874_ = lean_ctor_get(v___y_3873_, 0);
v___x_3875_ = lean_unbox(v_fst_3874_);
if (v___x_3875_ == 0)
{
lean_object* v_snd_3876_; 
v_snd_3876_ = lean_ctor_get(v___y_3873_, 1);
lean_inc(v_snd_3876_);
lean_dec_ref(v___y_3873_);
v_snd_3867_ = v_snd_3876_;
goto v___jp_3866_;
}
else
{
lean_object* v_snd_3877_; uint8_t v___x_3878_; 
lean_inc(v_fst_3874_);
lean_dec_ref(v___f_3806_);
v_snd_3877_ = lean_ctor_get(v___y_3873_, 1);
lean_inc(v_snd_3877_);
lean_dec_ref(v___y_3873_);
v___x_3878_ = lean_unbox(v_fst_3874_);
lean_dec(v_fst_3874_);
v_fst_3844_ = v___x_3878_;
v_snd_3845_ = v_snd_3877_;
goto v___jp_3843_;
}
}
}
else
{
lean_object* v_type_3886_; lean_object* v___x_3887_; uint8_t v_fst_3889_; lean_object* v_mctx_3890_; lean_object* v___y_3906_; lean_object* v_mctx_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_type_3886_ = lean_ctor_get(v_val_3800_, 3);
v___x_3887_ = lean_st_ref_get(v___y_3782_);
v_mctx_3911_ = lean_ctor_get(v___x_3887_, 0);
lean_inc_ref_n(v_mctx_3911_, 2);
lean_dec(v___x_3887_);
v___x_3912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v_mctx_3911_);
v___x_3914_ = l_Lean_Expr_hasFVar(v_type_3886_);
if (v___x_3914_ == 0)
{
uint8_t v___x_3915_; 
v___x_3915_ = l_Lean_Expr_hasMVar(v_type_3886_);
if (v___x_3915_ == 0)
{
lean_dec_ref_known(v___x_3913_, 2);
lean_dec_ref(v___f_3806_);
v_fst_3889_ = v___x_3915_;
v_mctx_3890_ = v_mctx_3911_;
goto v___jp_3888_;
}
else
{
lean_object* v___x_3916_; 
lean_dec_ref(v_mctx_3911_);
lean_inc_ref(v_type_3886_);
v___x_3916_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3886_, v___x_3913_);
v___y_3906_ = v___x_3916_;
goto v___jp_3905_;
}
}
else
{
lean_object* v___x_3917_; 
lean_dec_ref(v_mctx_3911_);
lean_inc_ref(v_type_3886_);
v___x_3917_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3806_, v___f_3805_, v_type_3886_, v___x_3913_);
v___y_3906_ = v___x_3917_;
goto v___jp_3905_;
}
v___jp_3888_:
{
lean_object* v___x_3891_; lean_object* v_cache_3892_; lean_object* v_zetaDeltaFVarIds_3893_; lean_object* v_postponed_3894_; lean_object* v_diag_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3903_; 
v___x_3891_ = lean_st_ref_take(v___y_3782_);
v_cache_3892_ = lean_ctor_get(v___x_3891_, 1);
v_zetaDeltaFVarIds_3893_ = lean_ctor_get(v___x_3891_, 2);
v_postponed_3894_ = lean_ctor_get(v___x_3891_, 3);
v_diag_3895_ = lean_ctor_get(v___x_3891_, 4);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v___x_3891_, 0);
lean_dec(v_unused_3904_);
v___x_3897_ = v___x_3891_;
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_diag_3895_);
lean_inc(v_postponed_3894_);
lean_inc(v_zetaDeltaFVarIds_3893_);
lean_inc(v_cache_3892_);
lean_dec(v___x_3891_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v_mctx_3890_);
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_mctx_3890_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_cache_3892_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_zetaDeltaFVarIds_3893_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_postponed_3894_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_diag_3895_);
v___x_3900_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_st_ref_put(v___y_3782_, v___x_3900_);
v_a_3802_ = v_fst_3889_;
goto v___jp_3801_;
}
}
}
v___jp_3905_:
{
lean_object* v_snd_3907_; lean_object* v_fst_3908_; lean_object* v_mctx_3909_; uint8_t v___x_3910_; 
v_snd_3907_ = lean_ctor_get(v___y_3906_, 1);
lean_inc(v_snd_3907_);
v_fst_3908_ = lean_ctor_get(v___y_3906_, 0);
lean_inc(v_fst_3908_);
lean_dec_ref(v___y_3906_);
v_mctx_3909_ = lean_ctor_get(v_snd_3907_, 1);
lean_inc_ref(v_mctx_3909_);
lean_dec(v_snd_3907_);
v___x_3910_ = lean_unbox(v_fst_3908_);
lean_dec(v_fst_3908_);
v_fst_3889_ = v___x_3910_;
v_mctx_3890_ = v_mctx_3909_;
goto v___jp_3888_;
}
}
}
v___jp_3801_:
{
if (v_a_3802_ == 0)
{
v_a_3792_ = v_snd_3786_;
goto v___jp_3791_;
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = l_Lean_LocalDecl_fvarId(v_val_3800_);
v___x_3804_ = lean_array_push(v_snd_3786_, v___x_3803_);
v_a_3792_ = v___x_3804_;
goto v___jp_3791_;
}
}
}
v___jp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v_a_3792_);
lean_ctor_set(v___x_3788_, 0, v___x_3790_);
v___x_3794_ = v___x_3788_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_a_3792_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
size_t v___x_3795_; size_t v___x_3796_; 
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3780_, v___x_3795_);
v_i_3780_ = v___x_3796_;
v_b_3781_ = v___x_3794_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3920_, lean_object* v_sz_3921_, lean_object* v_i_3922_, lean_object* v_b_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
size_t v_sz_boxed_3926_; size_t v_i_boxed_3927_; lean_object* v_res_3928_; 
v_sz_boxed_3926_ = lean_unbox_usize(v_sz_3921_);
lean_dec(v_sz_3921_);
v_i_boxed_3927_ = lean_unbox_usize(v_i_3922_);
lean_dec(v_i_3922_);
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3920_, v_sz_boxed_3926_, v_i_boxed_3927_, v_b_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v_as_3920_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3929_, size_t v_sz_3930_, size_t v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_usize_dec_lt(v_i_3931_, v_sz_3930_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_b_3932_);
return v___x_3939_;
}
else
{
lean_object* v_snd_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4072_; 
v_snd_3940_ = lean_ctor_get(v_b_3932_, 1);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_b_3932_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v_b_3932_, 0);
lean_dec(v_unused_4073_);
v___x_3942_ = v_b_3932_;
v_isShared_3943_ = v_isSharedCheck_4072_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_snd_3940_);
lean_dec(v_b_3932_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4072_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v_a_3946_; lean_object* v_a_3953_; 
v___x_3944_ = lean_box(0);
v_a_3953_ = lean_array_uget_borrowed(v_as_3929_, v_i_3931_);
if (lean_obj_tag(v_a_3953_) == 0)
{
v_a_3946_ = v_snd_3940_;
goto v___jp_3945_;
}
else
{
lean_object* v_val_3954_; uint8_t v_a_3956_; lean_object* v___f_3959_; lean_object* v___f_3960_; 
v_val_3954_ = lean_ctor_get(v_a_3953_, 0);
v___f_3959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3940_);
v___f_3960_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3960_, 0, v_snd_3940_);
if (lean_obj_tag(v_val_3954_) == 0)
{
lean_object* v_type_3961_; lean_object* v___x_3962_; uint8_t v_fst_3964_; lean_object* v_mctx_3965_; lean_object* v___y_3981_; lean_object* v_mctx_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; 
v_type_3961_ = lean_ctor_get(v_val_3954_, 3);
v___x_3962_ = lean_st_ref_get(v___y_3934_);
v_mctx_3986_ = lean_ctor_get(v___x_3962_, 0);
lean_inc_ref_n(v_mctx_3986_, 2);
lean_dec(v___x_3962_);
v___x_3987_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
lean_ctor_set(v___x_3988_, 1, v_mctx_3986_);
v___x_3989_ = l_Lean_Expr_hasFVar(v_type_3961_);
if (v___x_3989_ == 0)
{
uint8_t v___x_3990_; 
v___x_3990_ = l_Lean_Expr_hasMVar(v_type_3961_);
if (v___x_3990_ == 0)
{
lean_dec_ref_known(v___x_3988_, 2);
lean_dec_ref(v___f_3960_);
v_fst_3964_ = v___x_3990_;
v_mctx_3965_ = v_mctx_3986_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_3991_; 
lean_dec_ref(v_mctx_3986_);
lean_inc_ref(v_type_3961_);
v___x_3991_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_3961_, v___x_3988_);
v___y_3981_ = v___x_3991_;
goto v___jp_3980_;
}
}
else
{
lean_object* v___x_3992_; 
lean_dec_ref(v_mctx_3986_);
lean_inc_ref(v_type_3961_);
v___x_3992_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_3961_, v___x_3988_);
v___y_3981_ = v___x_3992_;
goto v___jp_3980_;
}
v___jp_3963_:
{
lean_object* v___x_3966_; lean_object* v_cache_3967_; lean_object* v_zetaDeltaFVarIds_3968_; lean_object* v_postponed_3969_; lean_object* v_diag_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
v___x_3966_ = lean_st_ref_take(v___y_3934_);
v_cache_3967_ = lean_ctor_get(v___x_3966_, 1);
v_zetaDeltaFVarIds_3968_ = lean_ctor_get(v___x_3966_, 2);
v_postponed_3969_ = lean_ctor_get(v___x_3966_, 3);
v_diag_3970_ = lean_ctor_get(v___x_3966_, 4);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v___x_3966_, 0);
lean_dec(v_unused_3979_);
v___x_3972_ = v___x_3966_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_diag_3970_);
lean_inc(v_postponed_3969_);
lean_inc(v_zetaDeltaFVarIds_3968_);
lean_inc(v_cache_3967_);
lean_dec(v___x_3966_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v_mctx_3965_);
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_mctx_3965_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_cache_3967_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_zetaDeltaFVarIds_3968_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_postponed_3969_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_diag_3970_);
v___x_3975_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_st_ref_put(v___y_3934_, v___x_3975_);
v_a_3956_ = v_fst_3964_;
goto v___jp_3955_;
}
}
}
v___jp_3980_:
{
lean_object* v_snd_3982_; lean_object* v_fst_3983_; lean_object* v_mctx_3984_; uint8_t v___x_3985_; 
v_snd_3982_ = lean_ctor_get(v___y_3981_, 1);
lean_inc(v_snd_3982_);
v_fst_3983_ = lean_ctor_get(v___y_3981_, 0);
lean_inc(v_fst_3983_);
lean_dec_ref(v___y_3981_);
v_mctx_3984_ = lean_ctor_get(v_snd_3982_, 1);
lean_inc_ref(v_mctx_3984_);
lean_dec(v_snd_3982_);
v___x_3985_ = lean_unbox(v_fst_3983_);
lean_dec(v_fst_3983_);
v_fst_3964_ = v___x_3985_;
v_mctx_3965_ = v_mctx_3984_;
goto v___jp_3963_;
}
}
else
{
uint8_t v_nondep_3993_; 
v_nondep_3993_ = lean_ctor_get_uint8(v_val_3954_, sizeof(void*)*5);
if (v_nondep_3993_ == 0)
{
lean_object* v_type_3994_; lean_object* v_value_3995_; lean_object* v___x_3996_; uint8_t v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___y_4016_; lean_object* v_snd_4021_; lean_object* v___y_4027_; lean_object* v_mctx_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_type_3994_ = lean_ctor_get(v_val_3954_, 3);
v_value_3995_ = lean_ctor_get(v_val_3954_, 4);
v___x_3996_ = lean_st_ref_get(v___y_3934_);
v_mctx_4033_ = lean_ctor_get(v___x_3996_, 0);
lean_inc_ref(v_mctx_4033_);
lean_dec(v___x_3996_);
v___x_4034_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v_mctx_4033_);
v___x_4036_ = l_Lean_Expr_hasFVar(v_type_3994_);
if (v___x_4036_ == 0)
{
uint8_t v___x_4037_; 
v___x_4037_ = l_Lean_Expr_hasMVar(v_type_3994_);
if (v___x_4037_ == 0)
{
v_snd_4021_ = v___x_4035_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4038_; 
lean_inc_ref(v_type_3994_);
lean_inc_ref(v___f_3960_);
v___x_4038_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_3994_, v___x_4035_);
v___y_4027_ = v___x_4038_;
goto v___jp_4026_;
}
}
else
{
lean_object* v___x_4039_; 
lean_inc_ref(v_type_3994_);
lean_inc_ref(v___f_3960_);
v___x_4039_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_3994_, v___x_4035_);
v___y_4027_ = v___x_4039_;
goto v___jp_4026_;
}
v___jp_3997_:
{
lean_object* v_mctx_4000_; lean_object* v___x_4001_; lean_object* v_cache_4002_; lean_object* v_zetaDeltaFVarIds_4003_; lean_object* v_postponed_4004_; lean_object* v_diag_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4013_; 
v_mctx_4000_ = lean_ctor_get(v_snd_3999_, 1);
lean_inc_ref(v_mctx_4000_);
lean_dec_ref(v_snd_3999_);
v___x_4001_ = lean_st_ref_take(v___y_3934_);
v_cache_4002_ = lean_ctor_get(v___x_4001_, 1);
v_zetaDeltaFVarIds_4003_ = lean_ctor_get(v___x_4001_, 2);
v_postponed_4004_ = lean_ctor_get(v___x_4001_, 3);
v_diag_4005_ = lean_ctor_get(v___x_4001_, 4);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v___x_4001_, 0);
lean_dec(v_unused_4014_);
v___x_4007_ = v___x_4001_;
v_isShared_4008_ = v_isSharedCheck_4013_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_diag_4005_);
lean_inc(v_postponed_4004_);
lean_inc(v_zetaDeltaFVarIds_4003_);
lean_inc(v_cache_4002_);
lean_dec(v___x_4001_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4013_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v_mctx_4000_);
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_mctx_4000_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_cache_4002_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_zetaDeltaFVarIds_4003_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_postponed_4004_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_diag_4005_);
v___x_4010_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_st_ref_put(v___y_3934_, v___x_4010_);
v_a_3956_ = v_fst_3998_;
goto v___jp_3955_;
}
}
}
v___jp_4015_:
{
lean_object* v_fst_4017_; lean_object* v_snd_4018_; uint8_t v___x_4019_; 
v_fst_4017_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_fst_4017_);
v_snd_4018_ = lean_ctor_get(v___y_4016_, 1);
lean_inc(v_snd_4018_);
lean_dec_ref(v___y_4016_);
v___x_4019_ = lean_unbox(v_fst_4017_);
lean_dec(v_fst_4017_);
v_fst_3998_ = v___x_4019_;
v_snd_3999_ = v_snd_4018_;
goto v___jp_3997_;
}
v___jp_4020_:
{
uint8_t v___x_4022_; 
v___x_4022_ = l_Lean_Expr_hasFVar(v_value_3995_);
if (v___x_4022_ == 0)
{
uint8_t v___x_4023_; 
v___x_4023_ = l_Lean_Expr_hasMVar(v_value_3995_);
if (v___x_4023_ == 0)
{
lean_dec_ref(v___f_3960_);
v_fst_3998_ = v___x_4023_;
v_snd_3999_ = v_snd_4021_;
goto v___jp_3997_;
}
else
{
lean_object* v___x_4024_; 
lean_inc_ref(v_value_3995_);
v___x_4024_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_value_3995_, v_snd_4021_);
v___y_4016_ = v___x_4024_;
goto v___jp_4015_;
}
}
else
{
lean_object* v___x_4025_; 
lean_inc_ref(v_value_3995_);
v___x_4025_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_value_3995_, v_snd_4021_);
v___y_4016_ = v___x_4025_;
goto v___jp_4015_;
}
}
v___jp_4026_:
{
lean_object* v_fst_4028_; uint8_t v___x_4029_; 
v_fst_4028_ = lean_ctor_get(v___y_4027_, 0);
v___x_4029_ = lean_unbox(v_fst_4028_);
if (v___x_4029_ == 0)
{
lean_object* v_snd_4030_; 
v_snd_4030_ = lean_ctor_get(v___y_4027_, 1);
lean_inc(v_snd_4030_);
lean_dec_ref(v___y_4027_);
v_snd_4021_ = v_snd_4030_;
goto v___jp_4020_;
}
else
{
lean_object* v_snd_4031_; uint8_t v___x_4032_; 
lean_inc(v_fst_4028_);
lean_dec_ref(v___f_3960_);
v_snd_4031_ = lean_ctor_get(v___y_4027_, 1);
lean_inc(v_snd_4031_);
lean_dec_ref(v___y_4027_);
v___x_4032_ = lean_unbox(v_fst_4028_);
lean_dec(v_fst_4028_);
v_fst_3998_ = v___x_4032_;
v_snd_3999_ = v_snd_4031_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_type_4040_; lean_object* v___x_4041_; uint8_t v_fst_4043_; lean_object* v_mctx_4044_; lean_object* v___y_4060_; lean_object* v_mctx_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v_type_4040_ = lean_ctor_get(v_val_3954_, 3);
v___x_4041_ = lean_st_ref_get(v___y_3934_);
v_mctx_4065_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_ref_n(v_mctx_4065_, 2);
lean_dec(v___x_4041_);
v___x_4066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
lean_ctor_set(v___x_4067_, 1, v_mctx_4065_);
v___x_4068_ = l_Lean_Expr_hasFVar(v_type_4040_);
if (v___x_4068_ == 0)
{
uint8_t v___x_4069_; 
v___x_4069_ = l_Lean_Expr_hasMVar(v_type_4040_);
if (v___x_4069_ == 0)
{
lean_dec_ref_known(v___x_4067_, 2);
lean_dec_ref(v___f_3960_);
v_fst_4043_ = v___x_4069_;
v_mctx_4044_ = v_mctx_4065_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4070_; 
lean_dec_ref(v_mctx_4065_);
lean_inc_ref(v_type_4040_);
v___x_4070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_4040_, v___x_4067_);
v___y_4060_ = v___x_4070_;
goto v___jp_4059_;
}
}
else
{
lean_object* v___x_4071_; 
lean_dec_ref(v_mctx_4065_);
lean_inc_ref(v_type_4040_);
v___x_4071_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3960_, v___f_3959_, v_type_4040_, v___x_4067_);
v___y_4060_ = v___x_4071_;
goto v___jp_4059_;
}
v___jp_4042_:
{
lean_object* v___x_4045_; lean_object* v_cache_4046_; lean_object* v_zetaDeltaFVarIds_4047_; lean_object* v_postponed_4048_; lean_object* v_diag_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4057_; 
v___x_4045_ = lean_st_ref_take(v___y_3934_);
v_cache_4046_ = lean_ctor_get(v___x_4045_, 1);
v_zetaDeltaFVarIds_4047_ = lean_ctor_get(v___x_4045_, 2);
v_postponed_4048_ = lean_ctor_get(v___x_4045_, 3);
v_diag_4049_ = lean_ctor_get(v___x_4045_, 4);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; 
v_unused_4058_ = lean_ctor_get(v___x_4045_, 0);
lean_dec(v_unused_4058_);
v___x_4051_ = v___x_4045_;
v_isShared_4052_ = v_isSharedCheck_4057_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_diag_4049_);
lean_inc(v_postponed_4048_);
lean_inc(v_zetaDeltaFVarIds_4047_);
lean_inc(v_cache_4046_);
lean_dec(v___x_4045_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4057_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v_mctx_4044_);
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_mctx_4044_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_cache_4046_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_zetaDeltaFVarIds_4047_);
lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_postponed_4048_);
lean_ctor_set(v_reuseFailAlloc_4056_, 4, v_diag_4049_);
v___x_4054_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_st_ref_put(v___y_3934_, v___x_4054_);
v_a_3956_ = v_fst_4043_;
goto v___jp_3955_;
}
}
}
v___jp_4059_:
{
lean_object* v_snd_4061_; lean_object* v_fst_4062_; lean_object* v_mctx_4063_; uint8_t v___x_4064_; 
v_snd_4061_ = lean_ctor_get(v___y_4060_, 1);
lean_inc(v_snd_4061_);
v_fst_4062_ = lean_ctor_get(v___y_4060_, 0);
lean_inc(v_fst_4062_);
lean_dec_ref(v___y_4060_);
v_mctx_4063_ = lean_ctor_get(v_snd_4061_, 1);
lean_inc_ref(v_mctx_4063_);
lean_dec(v_snd_4061_);
v___x_4064_ = lean_unbox(v_fst_4062_);
lean_dec(v_fst_4062_);
v_fst_4043_ = v___x_4064_;
v_mctx_4044_ = v_mctx_4063_;
goto v___jp_4042_;
}
}
}
v___jp_3955_:
{
if (v_a_3956_ == 0)
{
v_a_3946_ = v_snd_3940_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = l_Lean_LocalDecl_fvarId(v_val_3954_);
v___x_3958_ = lean_array_push(v_snd_3940_, v___x_3957_);
v_a_3946_ = v___x_3958_;
goto v___jp_3945_;
}
}
}
v___jp_3945_:
{
lean_object* v___x_3948_; 
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 1, v_a_3946_);
lean_ctor_set(v___x_3942_, 0, v___x_3944_);
v___x_3948_ = v___x_3942_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_a_3946_);
v___x_3948_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
size_t v___x_3949_; size_t v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = ((size_t)1ULL);
v___x_3950_ = lean_usize_add(v_i_3931_, v___x_3949_);
v___x_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3929_, v_sz_3930_, v___x_3950_, v___x_3948_, v___y_3934_);
return v___x_3951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4074_, lean_object* v_sz_4075_, lean_object* v_i_4076_, lean_object* v_b_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
size_t v_sz_boxed_4083_; size_t v_i_boxed_4084_; lean_object* v_res_4085_; 
v_sz_boxed_4083_ = lean_unbox_usize(v_sz_4075_);
lean_dec(v_sz_4075_);
v_i_boxed_4084_ = lean_unbox_usize(v_i_4076_);
lean_dec(v_i_4076_);
v_res_4085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4074_, v_sz_boxed_4083_, v_i_boxed_4084_, v_b_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec_ref(v_as_4074_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4086_, lean_object* v_init_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_root_4093_; lean_object* v_tail_4094_; lean_object* v___x_4095_; 
v_root_4093_ = lean_ctor_get(v_t_4086_, 0);
v_tail_4094_ = lean_ctor_get(v_t_4086_, 1);
lean_inc_ref(v_init_4087_);
v___x_4095_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4087_, v_root_4093_, v_init_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec_ref(v_init_4087_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4132_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4132_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4132_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
if (lean_obj_tag(v_a_4096_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4102_; 
v_a_4100_ = lean_ctor_get(v_a_4096_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v_a_4096_, 1);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v_a_4100_);
v___x_4102_ = v___x_4098_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; size_t v_sz_4107_; size_t v___x_4108_; lean_object* v___x_4109_; 
lean_del_object(v___x_4098_);
v_a_4104_ = lean_ctor_get(v_a_4096_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v_a_4096_, 1);
v___x_4105_ = lean_box(0);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v_a_4104_);
v_sz_4107_ = lean_array_size(v_tail_4094_);
v___x_4108_ = ((size_t)0ULL);
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4094_, v_sz_4107_, v___x_4108_, v___x_4106_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4123_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4123_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4123_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_fst_4114_; 
v_fst_4114_ = lean_ctor_get(v_a_4110_, 0);
if (lean_obj_tag(v_fst_4114_) == 0)
{
lean_object* v_snd_4115_; lean_object* v___x_4117_; 
v_snd_4115_ = lean_ctor_get(v_a_4110_, 1);
lean_inc(v_snd_4115_);
lean_dec(v_a_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v_snd_4115_);
v___x_4117_ = v___x_4112_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_snd_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
else
{
lean_object* v_val_4119_; lean_object* v___x_4121_; 
lean_inc_ref(v_fst_4114_);
lean_dec(v_a_4110_);
v_val_4119_ = lean_ctor_get(v_fst_4114_, 0);
lean_inc(v_val_4119_);
lean_dec_ref_known(v_fst_4114_, 1);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v_val_4119_);
v___x_4121_ = v___x_4112_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_val_4119_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v_a_4124_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4109_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4109_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4095_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4095_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4141_, lean_object* v_init_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4141_, v_init_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v_t_4141_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4149_, lean_object* v_fvarIds_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4156_; 
lean_inc(v_goal_4149_);
v___x_4156_ = l_Lean_MVarId_getDecl(v_goal_4149_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v_lctx_4158_; lean_object* v_decls_4159_; lean_object* v___x_4160_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v_lctx_4158_ = lean_ctor_get(v_a_4157_, 1);
lean_inc_ref(v_lctx_4158_);
lean_dec(v_a_4157_);
v_decls_4159_ = lean_ctor_get(v_lctx_4158_, 1);
lean_inc_ref(v_decls_4159_);
lean_dec_ref(v_lctx_4158_);
v___x_4160_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4159_, v_fvarIds_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
lean_dec_ref(v_decls_4159_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = l_Lean_MVarId_tryClearMany(v_goal_4149_, v_a_4161_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
lean_dec(v_a_4161_);
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec(v_goal_4149_);
v_a_4163_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4160_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4160_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec_ref(v_fvarIds_4150_);
lean_dec(v_goal_4149_);
v_a_4171_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4156_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4156_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4179_, lean_object* v_fvarIds_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4179_, v_fvarIds_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4187_, size_t v_sz_4188_, size_t v_i_4189_, lean_object* v_b_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4187_, v_sz_4188_, v_i_4189_, v_b_4190_, v___y_4192_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4197_, lean_object* v_sz_4198_, lean_object* v_i_4199_, lean_object* v_b_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
size_t v_sz_boxed_4206_; size_t v_i_boxed_4207_; lean_object* v_res_4208_; 
v_sz_boxed_4206_ = lean_unbox_usize(v_sz_4198_);
lean_dec(v_sz_4198_);
v_i_boxed_4207_ = lean_unbox_usize(v_i_4199_);
lean_dec(v_i_4199_);
v_res_4208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4197_, v_sz_boxed_4206_, v_i_boxed_4207_, v_b_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v_as_4197_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4209_, size_t v_sz_4210_, size_t v_i_4211_, lean_object* v_b_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4209_, v_sz_4210_, v_i_4211_, v_b_4212_, v___y_4214_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4219_, lean_object* v_sz_4220_, lean_object* v_i_4221_, lean_object* v_b_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
size_t v_sz_boxed_4228_; size_t v_i_boxed_4229_; lean_object* v_res_4230_; 
v_sz_boxed_4228_ = lean_unbox_usize(v_sz_4220_);
lean_dec(v_sz_4220_);
v_i_boxed_4229_ = lean_unbox_usize(v_i_4221_);
lean_dec(v_i_4221_);
v_res_4230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4219_, v_sz_boxed_4228_, v_i_boxed_4229_, v_b_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v_as_4219_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4231_, lean_object* v_as_4232_, size_t v_sz_4233_, size_t v_i_4234_, lean_object* v_b_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_usize_dec_lt(v_i_4234_, v_sz_4233_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v_b_4235_);
return v___x_4244_;
}
else
{
lean_object* v_a_4245_; lean_object* v_fst_4246_; lean_object* v_snd_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v_a_4245_ = lean_array_uget_borrowed(v_as_4232_, v_i_4234_);
v_fst_4246_ = lean_ctor_get(v_a_4245_, 0);
v_snd_4247_ = lean_ctor_get(v_a_4245_, 1);
v___x_4248_ = lean_box(0);
lean_inc(v_snd_4247_);
v___x_4249_ = l_Lean_Meta_FVarSubst_get(v_fs_4231_, v_snd_4247_);
lean_inc(v_fst_4246_);
v___x_4250_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4246_, v___x_4249_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
if (lean_obj_tag(v___x_4250_) == 0)
{
size_t v___x_4251_; size_t v___x_4252_; 
lean_dec_ref_known(v___x_4250_, 1);
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_add(v_i_4234_, v___x_4251_);
v_i_4234_ = v___x_4252_;
v_b_4235_ = v___x_4248_;
goto _start;
}
else
{
return v___x_4250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4254_, lean_object* v_as_4255_, lean_object* v_sz_4256_, lean_object* v_i_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
size_t v_sz_boxed_4266_; size_t v_i_boxed_4267_; lean_object* v_res_4268_; 
v_sz_boxed_4266_ = lean_unbox_usize(v_sz_4256_);
lean_dec(v_sz_4256_);
v_i_boxed_4267_ = lean_unbox_usize(v_i_4257_);
lean_dec(v_i_4257_);
v_res_4268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4254_, v_as_4255_, v_sz_boxed_4266_, v_i_boxed_4267_, v_b_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec_ref(v_as_4255_);
lean_dec(v_fs_4254_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4269_, lean_object* v_toTag_4270_, size_t v_sz_4271_, size_t v___x_4272_, lean_object* v___x_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4269_, v_toTag_4270_, v_sz_4271_, v___x_4272_, v___x_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4288_ == 0)
{
lean_object* v_unused_4289_; 
v_unused_4289_ = lean_ctor_get(v___x_4281_, 0);
lean_dec(v_unused_4289_);
v___x_4283_ = v___x_4281_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_dec(v___x_4281_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4273_);
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4273_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
else
{
return v___x_4281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4290_, lean_object* v_toTag_4291_, lean_object* v_sz_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
size_t v_sz_boxed_4302_; size_t v___x_1634__boxed_4303_; lean_object* v_res_4304_; 
v_sz_boxed_4302_ = lean_unbox_usize(v_sz_4292_);
lean_dec(v_sz_4292_);
v___x_1634__boxed_4303_ = lean_unbox_usize(v___x_4293_);
lean_dec(v___x_4293_);
v_res_4304_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4290_, v_toTag_4291_, v_sz_boxed_4302_, v___x_1634__boxed_4303_, v___x_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v_toTag_4291_);
lean_dec(v_fs_4290_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4305_, size_t v_i_4306_, size_t v_stop_4307_, lean_object* v_b_4308_){
_start:
{
lean_object* v___y_4310_; uint8_t v___x_4314_; 
v___x_4314_ = lean_usize_dec_eq(v_i_4306_, v_stop_4307_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = lean_array_uget_borrowed(v_as_4305_, v_i_4306_);
v___x_4316_ = l_Lean_Expr_isFVar(v___x_4315_);
if (v___x_4316_ == 0)
{
v___y_4310_ = v_b_4308_;
goto v___jp_4309_;
}
else
{
lean_object* v___x_4317_; 
lean_inc(v___x_4315_);
v___x_4317_ = lean_array_push(v_b_4308_, v___x_4315_);
v___y_4310_ = v___x_4317_;
goto v___jp_4309_;
}
}
else
{
return v_b_4308_;
}
v___jp_4309_:
{
size_t v___x_4311_; size_t v___x_4312_; 
v___x_4311_ = ((size_t)1ULL);
v___x_4312_ = lean_usize_add(v_i_4306_, v___x_4311_);
v_i_4306_ = v___x_4312_;
v_b_4308_ = v___y_4310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4318_, lean_object* v_i_4319_, lean_object* v_stop_4320_, lean_object* v_b_4321_){
_start:
{
size_t v_i_boxed_4322_; size_t v_stop_boxed_4323_; lean_object* v_res_4324_; 
v_i_boxed_4322_ = lean_unbox_usize(v_i_4319_);
lean_dec(v_i_4319_);
v_stop_boxed_4323_ = lean_unbox_usize(v_stop_4320_);
lean_dec(v_stop_4320_);
v_res_4324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4318_, v_i_boxed_4322_, v_stop_boxed_4323_, v_b_4321_);
lean_dec_ref(v_as_4318_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4325_, size_t v_sz_4326_, size_t v_i_4327_, lean_object* v_bs_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_lt(v_i_4327_, v_sz_4326_);
if (v___x_4329_ == 0)
{
return v_bs_4328_;
}
else
{
lean_object* v_v_4330_; lean_object* v___x_4331_; lean_object* v_bs_x27_4332_; lean_object* v___x_4333_; size_t v___x_4334_; size_t v___x_4335_; lean_object* v___x_4336_; 
v_v_4330_ = lean_array_uget(v_bs_4328_, v_i_4327_);
v___x_4331_ = lean_unsigned_to_nat(0u);
v_bs_x27_4332_ = lean_array_uset(v_bs_4328_, v_i_4327_, v___x_4331_);
v___x_4333_ = l_Lean_Meta_FVarSubst_get(v_fs_4325_, v_v_4330_);
v___x_4334_ = ((size_t)1ULL);
v___x_4335_ = lean_usize_add(v_i_4327_, v___x_4334_);
v___x_4336_ = lean_array_uset(v_bs_x27_4332_, v_i_4327_, v___x_4333_);
v_i_4327_ = v___x_4335_;
v_bs_4328_ = v___x_4336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4338_, lean_object* v_sz_4339_, lean_object* v_i_4340_, lean_object* v_bs_4341_){
_start:
{
size_t v_sz_boxed_4342_; size_t v_i_boxed_4343_; lean_object* v_res_4344_; 
v_sz_boxed_4342_ = lean_unbox_usize(v_sz_4339_);
lean_dec(v_sz_4339_);
v_i_boxed_4343_ = lean_unbox_usize(v_i_4340_);
lean_dec(v_i_4340_);
v_res_4344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4338_, v_sz_boxed_4342_, v_i_boxed_4343_, v_bs_4341_);
lean_dec(v_fs_4338_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4345_, size_t v_i_4346_, lean_object* v_bs_4347_){
_start:
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_usize_dec_lt(v_i_4346_, v_sz_4345_);
if (v___x_4348_ == 0)
{
return v_bs_4347_;
}
else
{
lean_object* v_v_4349_; lean_object* v___x_4350_; lean_object* v_bs_x27_4351_; lean_object* v___x_4352_; size_t v___x_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
v_v_4349_ = lean_array_uget(v_bs_4347_, v_i_4346_);
v___x_4350_ = lean_unsigned_to_nat(0u);
v_bs_x27_4351_ = lean_array_uset(v_bs_4347_, v_i_4346_, v___x_4350_);
v___x_4352_ = l_Lean_Expr_fvarId_x21(v_v_4349_);
lean_dec(v_v_4349_);
v___x_4353_ = ((size_t)1ULL);
v___x_4354_ = lean_usize_add(v_i_4346_, v___x_4353_);
v___x_4355_ = lean_array_uset(v_bs_x27_4351_, v_i_4346_, v___x_4352_);
v_i_4346_ = v___x_4354_;
v_bs_4347_ = v___x_4355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4357_, lean_object* v_i_4358_, lean_object* v_bs_4359_){
_start:
{
size_t v_sz_boxed_4360_; size_t v_i_boxed_4361_; lean_object* v_res_4362_; 
v_sz_boxed_4360_ = lean_unbox_usize(v_sz_4357_);
lean_dec(v_sz_4357_);
v_i_boxed_4361_ = lean_unbox_usize(v_i_4358_);
lean_dec(v_i_4358_);
v_res_4362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4360_, v_i_boxed_4361_, v_bs_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4367_, lean_object* v_g_4368_, lean_object* v_fs_4369_, lean_object* v_clears_4370_, lean_object* v_gs_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v___y_4380_; size_t v_sz_4417_; size_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v_sz_4417_ = lean_array_size(v_clears_4370_);
v___x_4418_ = ((size_t)0ULL);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4369_, v_sz_4417_, v___x_4418_, v_clears_4370_);
v___x_4420_ = lean_unsigned_to_nat(0u);
v___x_4421_ = lean_array_get_size(v___x_4419_);
v___x_4422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4423_ = lean_nat_dec_lt(v___x_4420_, v___x_4421_);
if (v___x_4423_ == 0)
{
lean_dec_ref(v___x_4419_);
v___y_4380_ = v___x_4422_;
goto v___jp_4379_;
}
else
{
size_t v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = lean_usize_of_nat(v___x_4421_);
v___x_4425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4419_, v___x_4418_, v___x_4424_, v___x_4422_);
lean_dec_ref(v___x_4419_);
v___y_4380_ = v___x_4425_;
goto v___jp_4379_;
}
v___jp_4379_:
{
size_t v_sz_4381_; size_t v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_sz_4381_ = lean_array_size(v___y_4380_);
v___x_4382_ = ((size_t)0ULL);
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4381_, v___x_4382_, v___y_4380_);
v___x_4384_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4368_, v___x_4383_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; size_t v_sz_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___f_4390_; lean_object* v___x_4391_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc_n(v_a_4385_, 2);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_box(0);
v_sz_4387_ = lean_array_size(v_toTag_4367_);
v___x_4388_ = lean_box_usize(v_sz_4387_);
v___x_4389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4390_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4390_, 0, v_fs_4369_);
lean_closure_set(v___f_4390_, 1, v_toTag_4367_);
lean_closure_set(v___f_4390_, 2, v___x_4388_);
lean_closure_set(v___f_4390_, 3, v___x_4389_);
lean_closure_set(v___f_4390_, 4, v___x_4386_);
v___x_4391_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4385_, v___f_4390_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4399_; 
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4399_ == 0)
{
lean_object* v_unused_4400_; 
v_unused_4400_ = lean_ctor_get(v___x_4391_, 0);
lean_dec(v_unused_4400_);
v___x_4393_ = v___x_4391_;
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
else
{
lean_dec(v___x_4391_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4395_ = lean_array_push(v_gs_4371_, v_a_4385_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4395_);
v___x_4397_ = v___x_4393_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4385_);
lean_dec_ref(v_gs_4371_);
v_a_4401_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4391_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4391_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v_gs_4371_);
lean_dec(v_fs_4369_);
lean_dec_ref(v_toTag_4367_);
v_a_4409_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4384_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4384_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4426_, lean_object* v_g_4427_, lean_object* v_fs_4428_, lean_object* v_clears_4429_, lean_object* v_gs_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4426_, v_g_4427_, v_fs_4428_, v_clears_4429_, v_gs_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
return v_res_4438_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4439_ = lean_box(0);
v___x_4440_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
lean_ctor_set(v___x_4441_, 1, v___x_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v___x_4505_; uint8_t v___x_4506_; 
v___x_4505_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4499_);
v___x_4506_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4505_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4507_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4499_);
v___x_4508_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4499_);
v___x_4510_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4499_);
v___x_4512_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4499_);
v___x_4514_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4499_);
v___x_4516_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4499_);
v___x_4518_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4499_);
v___x_4520_ = l_Lean_Syntax_isOfKind(v_stx_4499_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
lean_dec(v_stx_4499_);
v___x_4521_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_unsigned_to_nat(1u);
v___x_4523_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4522_);
v___x_4524_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4523_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4527_ = v___x_4524_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4524_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; lean_object* v___x_4531_; 
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v_stx_4499_);
lean_ctor_set(v___x_4529_, 1, v_a_4525_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4529_);
v___x_4531_ = v___x_4527_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
else
{
lean_dec(v_stx_4499_);
return v___x_4524_;
}
}
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_ps_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4534_ = lean_unsigned_to_nat(1u);
v___x_4535_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4534_);
v_ps_4536_ = l_Lean_Syntax_getArgs(v___x_4535_);
lean_dec(v___x_4535_);
v___x_4537_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4536_);
lean_dec_ref(v_ps_4536_);
v___x_4538_ = lean_array_to_list(v___x_4537_);
v___x_4539_ = lean_box(0);
v___x_4540_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4538_, v___x_4539_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4549_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4545_, 0, v_stx_4499_);
lean_ctor_set(v___x_4545_, 1, v_a_4541_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4545_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4557_; 
lean_dec(v_stx_4499_);
v_a_4550_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4552_ = v___x_4540_;
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4540_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4553_ == 0)
{
v___x_4555_ = v___x_4552_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = lean_unsigned_to_nat(1u);
v___x_4559_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4558_);
v___x_4560_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4559_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4565_, 0, v_stx_4499_);
lean_ctor_set(v___x_4565_, 1, v_a_4561_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
else
{
lean_dec(v_stx_4499_);
return v___x_4560_;
}
}
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4570_, 0, v_stx_4499_);
v___x_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4570_);
return v___x_4571_;
}
}
else
{
lean_object* v___x_4572_; lean_object* v_h_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v_h_4573_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4572_);
lean_dec(v_stx_4499_);
v___x_4574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4573_);
v___x_4575_ = l_Lean_Syntax_isOfKind(v_h_4573_, v___x_4574_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
lean_dec(v_h_4573_);
v___x_4576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4577_ = l_Lean_TSyntax_getId(v_h_4573_);
v___x_4578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4578_, 0, v_h_4573_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
}
else
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4581_, 0, v_stx_4499_);
lean_ctor_set(v___x_4581_, 1, v___x_4580_);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
return v___x_4582_;
}
}
else
{
lean_object* v___x_4583_; lean_object* v___x_4584_; uint8_t v___x_4585_; 
v___x_4583_ = lean_unsigned_to_nat(0u);
v___x_4584_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4583_);
lean_inc(v___x_4584_);
v___x_4585_ = l_Lean_Syntax_isOfKind(v___x_4584_, v___x_4505_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; 
lean_dec(v___x_4584_);
lean_dec(v_stx_4499_);
v___x_4586_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4586_;
}
else
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4587_ = lean_unsigned_to_nat(1u);
v___x_4588_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4587_);
v___x_4589_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4588_);
v___x_4590_ = l_Lean_Syntax_matchesNull(v___x_4588_, v___x_4589_);
if (v___x_4590_ == 0)
{
uint8_t v___x_4591_; 
lean_dec(v_stx_4499_);
v___x_4591_ = l_Lean_Syntax_matchesNull(v___x_4588_, v___x_4583_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_dec(v___x_4584_);
v___x_4592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4592_;
}
else
{
v_stx_4499_ = v___x_4584_;
goto _start;
}
}
else
{
lean_object* v_t_4594_; lean_object* v___x_4595_; 
v_t_4594_ = l_Lean_Syntax_getArg(v___x_4588_, v___x_4587_);
lean_dec(v___x_4588_);
v___x_4595_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4584_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4604_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4604_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4604_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4600_, 0, v_stx_4499_);
lean_ctor_set(v___x_4600_, 1, v_a_4596_);
lean_ctor_set(v___x_4600_, 2, v_t_4594_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4600_);
v___x_4602_ = v___x_4598_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
else
{
lean_dec(v_t_4594_);
lean_dec(v_stx_4499_);
return v___x_4595_;
}
}
}
}
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v_ps_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = l_Lean_Syntax_getArg(v_stx_4499_, v___x_4605_);
v_ps_4607_ = l_Lean_Syntax_getArgs(v___x_4606_);
lean_dec(v___x_4606_);
v___x_4608_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4607_);
lean_dec_ref(v_ps_4607_);
v___x_4609_ = lean_array_to_list(v___x_4608_);
v___x_4610_ = lean_box(0);
v___x_4611_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4609_, v___x_4610_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4620_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4620_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4620_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4616_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4499_, v_a_4612_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4616_);
v___x_4618_ = v___x_4614_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_dec(v_stx_4499_);
v_a_4621_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4611_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4611_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4629_, lean_object* v_x_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
if (lean_obj_tag(v_x_4629_) == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = l_List_reverse___redArg(v_x_4630_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
return v___x_4637_;
}
else
{
lean_object* v_head_4638_; lean_object* v_tail_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4657_; 
v_head_4638_ = lean_ctor_get(v_x_4629_, 0);
v_tail_4639_ = lean_ctor_get(v_x_4629_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4629_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4641_ = v_x_4629_;
v_isShared_4642_ = v_isSharedCheck_4657_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_tail_4639_);
lean_inc(v_head_4638_);
lean_dec(v_x_4629_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4657_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; 
v___x_4643_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4638_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4646_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v_x_4630_);
lean_ctor_set(v___x_4641_, 0, v_a_4644_);
v___x_4646_ = v___x_4641_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4644_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_x_4630_);
v___x_4646_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
v_x_4629_ = v_tail_4639_;
v_x_4630_ = v___x_4646_;
goto _start;
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
lean_del_object(v___x_4641_);
lean_dec(v_tail_4639_);
lean_dec(v_x_4630_);
v_a_4649_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4643_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4643_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4658_, lean_object* v_x_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4658_, v_x_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4673_, lean_object* v_as_4674_, size_t v_sz_4675_, size_t v_i_4676_, lean_object* v_b_4677_){
_start:
{
lean_object* v_a_4680_; uint8_t v___x_4684_; 
v___x_4684_ = lean_usize_dec_lt(v_i_4676_, v_sz_4675_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; 
v___x_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4685_, 0, v_b_4677_);
return v___x_4685_;
}
else
{
lean_object* v_fst_4686_; lean_object* v_snd_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4707_; 
v_fst_4686_ = lean_ctor_get(v_b_4677_, 0);
v_snd_4687_ = lean_ctor_get(v_b_4677_, 1);
v_isSharedCheck_4707_ = !lean_is_exclusive(v_b_4677_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4689_ = v_b_4677_;
v_isShared_4690_ = v_isSharedCheck_4707_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_snd_4687_);
lean_inc(v_fst_4686_);
lean_dec(v_b_4677_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4707_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v_a_4691_; lean_object* v_expr_4692_; lean_object* v_hName_x3f_4693_; lean_object* v___x_4694_; uint8_t v___x_4704_; 
v_a_4691_ = lean_array_uget_borrowed(v_as_4674_, v_i_4676_);
v_expr_4692_ = lean_ctor_get(v_a_4691_, 0);
v_hName_x3f_4693_ = lean_ctor_get(v_a_4691_, 2);
v___x_4694_ = lean_box(0);
v___x_4704_ = l_Lean_Expr_isFVar(v_expr_4692_);
if (v___x_4704_ == 0)
{
goto v___jp_4695_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4693_) == 0)
{
lean_object* v___x_4705_; lean_object* v___x_4706_; 
lean_del_object(v___x_4689_);
lean_inc_ref(v_expr_4692_);
v___x_4705_ = lean_array_push(v_fst_4686_, v_expr_4692_);
v___x_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set(v___x_4706_, 1, v_snd_4687_);
v_a_4680_ = v___x_4706_;
goto v___jp_4679_;
}
else
{
goto v___jp_4695_;
}
}
v___jp_4695_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4696_ = lean_array_get_borrowed(v___x_4694_, v_fst_4673_, v_snd_4687_);
lean_inc(v___x_4696_);
v___x_4697_ = l_Lean_mkFVar(v___x_4696_);
v___x_4698_ = lean_array_push(v_fst_4686_, v___x_4697_);
v___x_4699_ = lean_unsigned_to_nat(1u);
v___x_4700_ = lean_nat_add(v_snd_4687_, v___x_4699_);
lean_dec(v_snd_4687_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 1, v___x_4700_);
lean_ctor_set(v___x_4689_, 0, v___x_4698_);
v___x_4702_ = v___x_4689_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v___x_4700_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
v_a_4680_ = v___x_4702_;
goto v___jp_4679_;
}
}
}
}
v___jp_4679_:
{
size_t v___x_4681_; size_t v___x_4682_; 
v___x_4681_ = ((size_t)1ULL);
v___x_4682_ = lean_usize_add(v_i_4676_, v___x_4681_);
v_i_4676_ = v___x_4682_;
v_b_4677_ = v_a_4680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4708_, lean_object* v_as_4709_, lean_object* v_sz_4710_, lean_object* v_i_4711_, lean_object* v_b_4712_, lean_object* v___y_4713_){
_start:
{
size_t v_sz_boxed_4714_; size_t v_i_boxed_4715_; lean_object* v_res_4716_; 
v_sz_boxed_4714_ = lean_unbox_usize(v_sz_4710_);
lean_dec(v_sz_4710_);
v_i_boxed_4715_ = lean_unbox_usize(v_i_4711_);
lean_dec(v_i_4711_);
v_res_4716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4708_, v_as_4709_, v_sz_boxed_4714_, v_i_boxed_4715_, v_b_4712_);
lean_dec_ref(v_as_4709_);
lean_dec_ref(v_fst_4708_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4717_, size_t v_i_4718_, size_t v_stop_4719_, lean_object* v_b_4720_){
_start:
{
lean_object* v___y_4722_; uint8_t v___x_4726_; 
v___x_4726_ = lean_usize_dec_eq(v_i_4718_, v_stop_4719_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; lean_object* v_expr_4728_; lean_object* v_hName_x3f_4729_; uint8_t v___x_4730_; 
v___x_4727_ = lean_array_uget_borrowed(v_as_4717_, v_i_4718_);
v_expr_4728_ = lean_ctor_get(v___x_4727_, 0);
v_hName_x3f_4729_ = lean_ctor_get(v___x_4727_, 2);
v___x_4730_ = l_Lean_Expr_isFVar(v_expr_4728_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; 
lean_inc(v___x_4727_);
v___x_4731_ = lean_array_push(v_b_4720_, v___x_4727_);
v___y_4722_ = v___x_4731_;
goto v___jp_4721_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4729_) == 0)
{
v___y_4722_ = v_b_4720_;
goto v___jp_4721_;
}
else
{
lean_object* v___x_4732_; 
lean_inc(v___x_4727_);
v___x_4732_ = lean_array_push(v_b_4720_, v___x_4727_);
v___y_4722_ = v___x_4732_;
goto v___jp_4721_;
}
}
}
else
{
return v_b_4720_;
}
v___jp_4721_:
{
size_t v___x_4723_; size_t v___x_4724_; 
v___x_4723_ = ((size_t)1ULL);
v___x_4724_ = lean_usize_add(v_i_4718_, v___x_4723_);
v_i_4718_ = v___x_4724_;
v_b_4720_ = v___y_4722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4733_, lean_object* v_i_4734_, lean_object* v_stop_4735_, lean_object* v_b_4736_){
_start:
{
size_t v_i_boxed_4737_; size_t v_stop_boxed_4738_; lean_object* v_res_4739_; 
v_i_boxed_4737_ = lean_unbox_usize(v_i_4734_);
lean_dec(v_i_4734_);
v_stop_boxed_4738_ = lean_unbox_usize(v_stop_4735_);
lean_dec(v_stop_4735_);
v_res_4739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4733_, v_i_boxed_4737_, v_stop_boxed_4738_, v_b_4736_);
lean_dec_ref(v_as_4733_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4745_, lean_object* v_args_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v_lower_4756_; lean_object* v_upper_4757_; lean_object* v_j_4763_; lean_object* v___y_4765_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v_j_4763_ = lean_unsigned_to_nat(0u);
v___x_4796_ = lean_array_get_size(v_args_4746_);
v___x_4797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4798_ = lean_nat_dec_lt(v_j_4763_, v___x_4796_);
if (v___x_4798_ == 0)
{
v___y_4765_ = v___x_4797_;
goto v___jp_4764_;
}
else
{
size_t v___x_4799_; size_t v___x_4800_; lean_object* v___x_4801_; 
v___x_4799_ = ((size_t)0ULL);
v___x_4800_ = lean_usize_of_nat(v___x_4796_);
v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4746_, v___x_4799_, v___x_4800_, v___x_4797_);
v___y_4765_ = v___x_4801_;
goto v___jp_4764_;
}
v___jp_4752_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4758_ = l_Array_toSubarray___redArg(v___y_4753_, v_lower_4756_, v_upper_4757_);
v___x_4759_ = l_Subarray_copy___redArg(v___x_4758_);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
lean_ctor_set(v___x_4760_, 1, v___y_4755_);
v___x_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___y_4754_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
v___jp_4764_:
{
uint8_t v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = 3;
v___x_4767_ = l_Lean_MVarId_generalize(v_goal_4745_, v___y_4765_, v___x_4766_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_object* v_a_4768_; lean_object* v_fst_4769_; lean_object* v_snd_4770_; lean_object* v___x_4771_; size_t v_sz_4772_; size_t v___x_4773_; lean_object* v___x_4774_; 
v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v___x_4767_, 1);
v_fst_4769_ = lean_ctor_get(v_a_4768_, 0);
lean_inc(v_fst_4769_);
v_snd_4770_ = lean_ctor_get(v_a_4768_, 1);
lean_inc(v_snd_4770_);
lean_dec(v_a_4768_);
v___x_4771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4772_ = lean_array_size(v_args_4746_);
v___x_4773_ = ((size_t)0ULL);
v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4769_, v_args_4746_, v_sz_4772_, v___x_4773_, v___x_4771_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; lean_object* v_fst_4776_; lean_object* v_snd_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v___x_4774_, 1);
v_fst_4776_ = lean_ctor_get(v_a_4775_, 0);
lean_inc(v_fst_4776_);
v_snd_4777_ = lean_ctor_get(v_a_4775_, 1);
lean_inc(v_snd_4777_);
lean_dec(v_a_4775_);
v___x_4778_ = lean_array_get_size(v_fst_4769_);
v___x_4779_ = lean_nat_dec_le(v_snd_4777_, v_j_4763_);
if (v___x_4779_ == 0)
{
v___y_4753_ = v_fst_4769_;
v___y_4754_ = v_fst_4776_;
v___y_4755_ = v_snd_4770_;
v_lower_4756_ = v_snd_4777_;
v_upper_4757_ = v___x_4778_;
goto v___jp_4752_;
}
else
{
lean_dec(v_snd_4777_);
v___y_4753_ = v_fst_4769_;
v___y_4754_ = v_fst_4776_;
v___y_4755_ = v_snd_4770_;
v_lower_4756_ = v_j_4763_;
v_upper_4757_ = v___x_4778_;
goto v___jp_4752_;
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_dec(v_snd_4770_);
lean_dec(v_fst_4769_);
v_a_4780_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4774_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4774_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
v_a_4788_ = lean_ctor_get(v___x_4767_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4767_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4767_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4802_, lean_object* v_args_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4802_, v_args_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec_ref(v_args_4803_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4810_, lean_object* v_as_4811_, size_t v_sz_4812_, size_t v_i_4813_, lean_object* v_b_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4810_, v_as_4811_, v_sz_4812_, v_i_4813_, v_b_4814_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4821_, lean_object* v_as_4822_, lean_object* v_sz_4823_, lean_object* v_i_4824_, lean_object* v_b_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
size_t v_sz_boxed_4831_; size_t v_i_boxed_4832_; lean_object* v_res_4833_; 
v_sz_boxed_4831_ = lean_unbox_usize(v_sz_4823_);
lean_dec(v_sz_4823_);
v_i_boxed_4832_ = lean_unbox_usize(v_i_4824_);
lean_dec(v_i_4824_);
v_res_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4821_, v_as_4822_, v_sz_boxed_4831_, v_i_boxed_4832_, v_b_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec_ref(v_as_4822_);
lean_dec_ref(v_fst_4821_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4834_, size_t v_i_4835_, size_t v_stop_4836_, lean_object* v_b_4837_){
_start:
{
lean_object* v___y_4839_; uint8_t v___x_4843_; 
v___x_4843_ = lean_usize_dec_eq(v_i_4835_, v_stop_4836_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; lean_object* v_fst_4845_; 
v___x_4844_ = lean_array_uget_borrowed(v_as_4834_, v_i_4835_);
v_fst_4845_ = lean_ctor_get(v___x_4844_, 0);
if (lean_obj_tag(v_fst_4845_) == 0)
{
v___y_4839_ = v_b_4837_;
goto v___jp_4838_;
}
else
{
lean_object* v_val_4846_; lean_object* v___x_4847_; 
v_val_4846_ = lean_ctor_get(v_fst_4845_, 0);
lean_inc(v_val_4846_);
v___x_4847_ = lean_array_push(v_b_4837_, v_val_4846_);
v___y_4839_ = v___x_4847_;
goto v___jp_4838_;
}
}
else
{
return v_b_4837_;
}
v___jp_4838_:
{
size_t v___x_4840_; size_t v___x_4841_; 
v___x_4840_ = ((size_t)1ULL);
v___x_4841_ = lean_usize_add(v_i_4835_, v___x_4840_);
v_i_4835_ = v___x_4841_;
v_b_4837_ = v___y_4839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4848_, lean_object* v_i_4849_, lean_object* v_stop_4850_, lean_object* v_b_4851_){
_start:
{
size_t v_i_boxed_4852_; size_t v_stop_boxed_4853_; lean_object* v_res_4854_; 
v_i_boxed_4852_ = lean_unbox_usize(v_i_4849_);
lean_dec(v_i_4849_);
v_stop_boxed_4853_ = lean_unbox_usize(v_stop_4850_);
lean_dec(v_stop_4850_);
v_res_4854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4848_, v_i_boxed_4852_, v_stop_boxed_4853_, v_b_4851_);
lean_dec_ref(v_as_4848_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4857_, lean_object* v_start_4858_, lean_object* v_stop_4859_){
_start:
{
lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4860_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4861_ = lean_nat_dec_lt(v_start_4858_, v_stop_4859_);
if (v___x_4861_ == 0)
{
return v___x_4860_;
}
else
{
lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4862_ = lean_array_get_size(v_as_4857_);
v___x_4863_ = lean_nat_dec_le(v_stop_4859_, v___x_4862_);
if (v___x_4863_ == 0)
{
uint8_t v___x_4864_; 
v___x_4864_ = lean_nat_dec_lt(v_start_4858_, v___x_4862_);
if (v___x_4864_ == 0)
{
return v___x_4860_;
}
else
{
size_t v___x_4865_; size_t v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = lean_usize_of_nat(v_start_4858_);
v___x_4866_ = lean_usize_of_nat(v___x_4862_);
v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4857_, v___x_4865_, v___x_4866_, v___x_4860_);
return v___x_4867_;
}
}
else
{
size_t v___x_4868_; size_t v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = lean_usize_of_nat(v_start_4858_);
v___x_4869_ = lean_usize_of_nat(v_stop_4859_);
v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4857_, v___x_4868_, v___x_4869_, v___x_4860_);
return v___x_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4871_, lean_object* v_start_4872_, lean_object* v_stop_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4871_, v_start_4872_, v_stop_4873_);
lean_dec(v_stop_4873_);
lean_dec(v_start_4872_);
lean_dec_ref(v_as_4871_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4875_, lean_object* v_bs_4876_, lean_object* v_i_4877_, lean_object* v_cs_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; lean_object* v___x_4897_; uint8_t v___x_4898_; 
v___x_4897_ = lean_array_get_size(v_as_4875_);
v___x_4898_ = lean_nat_dec_lt(v_i_4877_, v___x_4897_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; 
lean_dec(v_i_4877_);
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v_cs_4878_);
return v___x_4899_;
}
else
{
lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4900_ = lean_array_get_size(v_bs_4876_);
v___x_4901_ = lean_nat_dec_lt(v_i_4877_, v___x_4900_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; 
lean_dec(v_i_4877_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v_cs_4878_);
return v___x_4902_;
}
else
{
lean_object* v_a_4903_; lean_object* v_fst_4904_; lean_object* v_snd_4905_; lean_object* v_fst_4907_; lean_object* v_snd_4908_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___y_4914_; lean_object* v_b_4946_; 
v_a_4903_ = lean_array_fget_borrowed(v_as_4875_, v_i_4877_);
v_fst_4904_ = lean_ctor_get(v_a_4903_, 0);
lean_inc(v_fst_4904_);
v_snd_4905_ = lean_ctor_get(v_a_4903_, 1);
v_b_4946_ = lean_array_fget(v_bs_4876_, v_i_4877_);
if (lean_obj_tag(v_b_4946_) == 4)
{
lean_object* v_ref_4947_; lean_object* v_a_4948_; lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4985_; 
v_ref_4947_ = lean_ctor_get(v_b_4946_, 0);
v_a_4948_ = lean_ctor_get(v_b_4946_, 1);
v_a_4949_ = lean_ctor_get(v_b_4946_, 2);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_b_4946_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4951_ = v_b_4946_;
v_isShared_4952_ = v_isSharedCheck_4985_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc(v_ref_4947_);
lean_dec(v_b_4946_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4985_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v_toCold_4953_; lean_object* v_currRecDepth_4954_; lean_object* v_ref_4955_; uint16_t v_optionFlags_4956_; uint8_t v_suppressElabErrors_4957_; uint8_t v_isRecordingDeps_4958_; lean_object* v_ref_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v_toCold_4953_ = lean_ctor_get(v___y_4883_, 0);
v_currRecDepth_4954_ = lean_ctor_get(v___y_4883_, 1);
v_ref_4955_ = lean_ctor_get(v___y_4883_, 2);
v_optionFlags_4956_ = lean_ctor_get_uint16(v___y_4883_, sizeof(void*)*3);
v_suppressElabErrors_4957_ = lean_ctor_get_uint8(v___y_4883_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4958_ = lean_ctor_get_uint8(v___y_4883_, sizeof(void*)*3 + 3);
v_ref_4959_ = l_Lean_replaceRef(v_ref_4947_, v_ref_4955_);
lean_inc(v_currRecDepth_4954_);
lean_inc_ref(v_toCold_4953_);
v___x_4960_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4960_, 0, v_toCold_4953_);
lean_ctor_set(v___x_4960_, 1, v_currRecDepth_4954_);
lean_ctor_set(v___x_4960_, 2, v_ref_4959_);
lean_ctor_set_uint16(v___x_4960_, sizeof(void*)*3, v_optionFlags_4956_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*3 + 2, v_suppressElabErrors_4957_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*3 + 3, v_isRecordingDeps_4958_);
v___x_4961_ = l_Lean_Elab_Term_elabType(v_a_4949_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___x_4960_, v___y_4884_);
if (lean_obj_tag(v___x_4961_) == 0)
{
lean_object* v_a_4962_; lean_object* v___x_4963_; 
v_a_4962_ = lean_ctor_get(v___x_4961_, 0);
lean_inc_n(v_a_4962_, 2);
lean_dec_ref_known(v___x_4961_, 1);
v___x_4963_ = l_Lean_Elab_Term_exprToSyntax(v_a_4962_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___x_4960_, v___y_4884_);
lean_dec_ref_known(v___x_4960_, 3);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4966_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 2, v_a_4964_);
v___x_4966_ = v___x_4951_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_ref_4947_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v_a_4948_);
lean_ctor_set(v_reuseFailAlloc_4968_, 2, v_a_4964_);
v___x_4966_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
lean_object* v___x_4967_; 
v___x_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_a_4962_);
v_fst_4907_ = v___x_4966_;
v_snd_4908_ = v___x_4967_;
v___y_4909_ = v___y_4879_;
v___y_4910_ = v___y_4880_;
v___y_4911_ = v___y_4881_;
v___y_4912_ = v___y_4882_;
v___y_4913_ = v___y_4883_;
v___y_4914_ = v___y_4884_;
goto v___jp_4906_;
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v_a_4962_);
lean_del_object(v___x_4951_);
lean_dec_ref(v_a_4948_);
lean_dec(v_ref_4947_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_cs_4878_);
lean_dec(v_i_4877_);
v_a_4969_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4963_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4963_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec_ref_known(v___x_4960_, 3);
lean_del_object(v___x_4951_);
lean_dec_ref(v_a_4948_);
lean_dec(v_ref_4947_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_cs_4878_);
lean_dec(v_i_4877_);
v_a_4977_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4961_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4961_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
}
else
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_box(0);
v_fst_4907_ = v_b_4946_;
v_snd_4908_ = v___x_4986_;
v___y_4909_ = v___y_4879_;
v___y_4910_ = v___y_4880_;
v___y_4911_ = v___y_4881_;
v___y_4912_ = v___y_4882_;
v___y_4913_ = v___y_4883_;
v___y_4914_ = v___y_4884_;
goto v___jp_4906_;
}
v___jp_4906_:
{
lean_object* v___x_4915_; 
lean_inc(v_snd_4908_);
lean_inc(v_snd_4905_);
v___x_4915_ = l_Lean_Elab_Term_elabTerm(v_snd_4905_, v_snd_4908_, v___x_4901_, v___x_4901_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = lean_box(0);
v___x_4918_ = l_Lean_Elab_Term_ensureHasType(v_snd_4908_, v_a_4916_, v___x_4917_, v___x_4917_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4920_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_a_4919_);
lean_dec_ref_known(v___x_4918_, 1);
v___x_4920_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4907_);
if (lean_obj_tag(v_fst_4904_) == 0)
{
v___y_4887_ = v_fst_4907_;
v___y_4888_ = v_a_4919_;
v___y_4889_ = v___x_4920_;
v___y_4890_ = v___x_4917_;
goto v___jp_4886_;
}
else
{
lean_object* v_val_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4929_; 
v_val_4921_ = lean_ctor_get(v_fst_4904_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v_fst_4904_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4923_ = v_fst_4904_;
v_isShared_4924_ = v_isSharedCheck_4929_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_val_4921_);
lean_dec(v_fst_4904_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4929_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4927_; 
v___x_4925_ = l_Lean_TSyntax_getId(v_val_4921_);
lean_dec(v_val_4921_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4925_);
v___x_4927_ = v___x_4923_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
v___y_4887_ = v_fst_4907_;
v___y_4888_ = v_a_4919_;
v___y_4889_ = v___x_4920_;
v___y_4890_ = v___x_4927_;
goto v___jp_4886_;
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec_ref(v_fst_4907_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_cs_4878_);
lean_dec(v_i_4877_);
v_a_4930_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4918_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4918_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_snd_4908_);
lean_dec_ref(v_fst_4907_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_cs_4878_);
lean_dec(v_i_4877_);
v_a_4938_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4915_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4915_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
v___jp_4886_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4891_, 0, v___y_4888_);
lean_ctor_set(v___x_4891_, 1, v___y_4889_);
lean_ctor_set(v___x_4891_, 2, v___y_4890_);
v___x_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___y_4887_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = lean_unsigned_to_nat(1u);
v___x_4894_ = lean_nat_add(v_i_4877_, v___x_4893_);
lean_dec(v_i_4877_);
v___x_4895_ = lean_array_push(v_cs_4878_, v___x_4892_);
v_i_4877_ = v___x_4894_;
v_cs_4878_ = v___x_4895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_4987_, lean_object* v_bs_4988_, lean_object* v_i_4989_, lean_object* v_cs_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_4987_, v_bs_4988_, v_i_4989_, v_cs_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
lean_dec_ref(v_bs_4988_);
lean_dec_ref(v_as_4987_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5001_, lean_object* v_g_5002_, lean_object* v_pats_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5011_ = lean_array_mk(v_pats_5003_);
v___x_5012_ = lean_unsigned_to_nat(0u);
v___x_5013_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5014_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5001_, v___x_5011_, v___x_5012_, v___x_5013_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
lean_dec_ref(v___x_5011_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5016_; lean_object* v_fst_5017_; lean_object* v_snd_5018_; lean_object* v___x_5019_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
v___x_5016_ = l_Array_unzip___redArg(v_a_5015_);
lean_dec(v_a_5015_);
v_fst_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_fst_5017_);
v_snd_5018_ = lean_ctor_get(v___x_5016_, 1);
lean_inc(v_snd_5018_);
lean_dec_ref(v___x_5016_);
v___x_5019_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5002_, v_snd_5018_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
lean_dec(v_snd_5018_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v_snd_5021_; lean_object* v_fst_5022_; lean_object* v_fst_5023_; lean_object* v_snd_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref_known(v___x_5019_, 1);
v_snd_5021_ = lean_ctor_get(v_a_5020_, 1);
lean_inc(v_snd_5021_);
v_fst_5022_ = lean_ctor_get(v_a_5020_, 0);
lean_inc(v_fst_5022_);
lean_dec(v_a_5020_);
v_fst_5023_ = lean_ctor_get(v_snd_5021_, 0);
lean_inc(v_fst_5023_);
v_snd_5024_ = lean_ctor_get(v_snd_5021_, 1);
lean_inc(v_snd_5024_);
lean_dec(v_snd_5021_);
v___x_5025_ = lean_array_get_size(v_tgts_5001_);
v___x_5026_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5001_, v___x_5012_, v___x_5025_);
v___x_5027_ = l_Array_zip___redArg(v___x_5026_, v_fst_5023_);
lean_dec(v_fst_5023_);
lean_dec_ref(v___x_5026_);
v___x_5028_ = lean_box(0);
v___x_5029_ = l_Array_zip___redArg(v_fst_5017_, v_fst_5022_);
lean_dec(v_fst_5022_);
lean_dec(v_fst_5017_);
v___x_5030_ = lean_array_to_list(v___x_5029_);
v___x_5031_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5031_, 0, v___x_5027_);
v___x_5032_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5024_, v___x_5028_, v___x_5013_, v___x_5013_, v___x_5030_, v___x_5031_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5041_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5035_ = v___x_5032_;
v_isShared_5036_ = v_isSharedCheck_5041_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5032_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5041_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5037_; lean_object* v___x_5039_; 
v___x_5037_ = lean_array_to_list(v_a_5033_);
if (v_isShared_5036_ == 0)
{
lean_ctor_set(v___x_5035_, 0, v___x_5037_);
v___x_5039_ = v___x_5035_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
v_a_5042_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5032_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5032_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_fst_5017_);
v_a_5050_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5019_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5019_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec(v_g_5002_);
v_a_5058_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5014_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5014_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5066_, lean_object* v_g_5067_, lean_object* v_pats_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5066_, v_g_5067_, v_pats_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec_ref(v_tgts_5066_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5077_, size_t v_sz_5078_, size_t v_i_5079_, lean_object* v_bs_5080_){
_start:
{
uint8_t v___x_5081_; 
v___x_5081_ = lean_usize_dec_lt(v_i_5079_, v_sz_5078_);
if (v___x_5081_ == 0)
{
return v_bs_5080_;
}
else
{
lean_object* v___x_5082_; uint8_t v___x_5083_; lean_object* v___x_5084_; lean_object* v_bs_x27_5085_; uint8_t v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; size_t v___x_5089_; size_t v___x_5090_; lean_object* v___x_5091_; 
v___x_5082_ = lean_unsigned_to_nat(1u);
v___x_5083_ = lean_nat_dec_eq(v___x_5077_, v___x_5082_);
v___x_5084_ = lean_unsigned_to_nat(0u);
v_bs_x27_5085_ = lean_array_uset(v_bs_5080_, v_i_5079_, v___x_5084_);
v___x_5086_ = 0;
v___x_5087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_5088_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5088_, 0, v___x_5087_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1, v___x_5086_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 1, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 2, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 3, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 4, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 5, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*1 + 6, v___x_5083_);
v___x_5089_ = ((size_t)1ULL);
v___x_5090_ = lean_usize_add(v_i_5079_, v___x_5089_);
v___x_5091_ = lean_array_uset(v_bs_x27_5085_, v_i_5079_, v___x_5088_);
v_i_5079_ = v___x_5090_;
v_bs_5080_ = v___x_5091_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5093_, lean_object* v_sz_5094_, lean_object* v_i_5095_, lean_object* v_bs_5096_){
_start:
{
size_t v_sz_boxed_5097_; size_t v_i_boxed_5098_; lean_object* v_res_5099_; 
v_sz_boxed_5097_ = lean_unbox_usize(v_sz_5094_);
lean_dec(v_sz_5094_);
v_i_boxed_5098_ = lean_unbox_usize(v_i_5095_);
lean_dec(v_i_5095_);
v_res_5099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5093_, v_sz_boxed_5097_, v_i_boxed_5098_, v_bs_5096_);
lean_dec(v___x_5093_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5100_, lean_object* v___x_5101_, lean_object* v_pat_5102_, lean_object* v_tgts_5103_, lean_object* v___x_5104_, lean_object* v___f_5105_, lean_object* v_g_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
if (v___x_5100_ == 0)
{
lean_object* v___x_5114_; uint8_t v___x_5115_; lean_object* v___y_5117_; 
lean_dec(v_g_5106_);
v___x_5114_ = lean_unsigned_to_nat(1u);
v___x_5115_ = lean_nat_dec_eq(v___x_5101_, v___x_5114_);
if (v___x_5115_ == 0)
{
lean_object* v_ref_5126_; 
v_ref_5126_ = lean_ctor_get(v_pat_5102_, 0);
lean_inc(v_ref_5126_);
v___y_5117_ = v_ref_5126_;
goto v___jp_5116_;
}
else
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
lean_dec_ref(v_tgts_5103_);
v___x_5127_ = lean_box(0);
v___x_5128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5128_, 0, v_pat_5102_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
v___x_5129_ = lean_apply_8(v___f_5105_, v___x_5128_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, lean_box(0));
return v___x_5129_;
}
v___jp_5116_:
{
lean_object* v___x_5118_; lean_object* v_snd_5119_; size_t v_sz_5120_; size_t v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v_snd_5124_; lean_object* v___x_5125_; 
v___x_5118_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5102_);
v_snd_5119_ = lean_ctor_get(v___x_5118_, 1);
lean_inc(v_snd_5119_);
lean_dec_ref(v___x_5118_);
v_sz_5120_ = lean_array_size(v_tgts_5103_);
v___x_5121_ = ((size_t)0ULL);
v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5101_, v_sz_5120_, v___x_5121_, v_tgts_5103_);
v___x_5123_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5117_, v___x_5122_, v___x_5115_, v___x_5104_, v_snd_5119_);
lean_dec_ref(v___x_5122_);
v_snd_5124_ = lean_ctor_get(v___x_5123_, 1);
lean_inc(v_snd_5124_);
lean_dec_ref(v___x_5123_);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
v___x_5125_ = lean_apply_8(v___f_5105_, v_snd_5124_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, lean_box(0));
return v___x_5125_;
}
}
else
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
lean_dec_ref(v___f_5105_);
lean_dec_ref(v_tgts_5103_);
lean_dec_ref(v_pat_5102_);
v___x_5130_ = lean_box(0);
v___x_5131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5131_, 0, v_g_5106_);
lean_ctor_set(v___x_5131_, 1, v___x_5130_);
v___x_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5131_);
return v___x_5132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5133_, lean_object* v___x_5134_, lean_object* v_pat_5135_, lean_object* v_tgts_5136_, lean_object* v___x_5137_, lean_object* v___f_5138_, lean_object* v_g_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
uint8_t v___x_5027__boxed_5147_; lean_object* v_res_5148_; 
v___x_5027__boxed_5147_ = lean_unbox(v___x_5133_);
v_res_5148_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5027__boxed_5147_, v___x_5134_, v_pat_5135_, v_tgts_5136_, v___x_5137_, v___f_5138_, v_g_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___x_5137_);
lean_dec(v___x_5134_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5149_, lean_object* v_pat_5150_, lean_object* v_g_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v___f_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; lean_object* v___x_5163_; lean_object* v___y_5164_; uint8_t v___x_5165_; lean_object* v___x_5166_; 
lean_inc(v_g_5151_);
lean_inc_ref(v_tgts_5149_);
v___f_5159_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5159_, 0, v_tgts_5149_);
lean_closure_set(v___f_5159_, 1, v_g_5151_);
v___x_5160_ = lean_array_get_size(v_tgts_5149_);
v___x_5161_ = lean_unsigned_to_nat(0u);
v___x_5162_ = lean_nat_dec_eq(v___x_5160_, v___x_5161_);
v___x_5163_ = lean_box(v___x_5162_);
v___y_5164_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5164_, 0, v___x_5163_);
lean_closure_set(v___y_5164_, 1, v___x_5160_);
lean_closure_set(v___y_5164_, 2, v_pat_5150_);
lean_closure_set(v___y_5164_, 3, v_tgts_5149_);
lean_closure_set(v___y_5164_, 4, v___x_5161_);
lean_closure_set(v___y_5164_, 5, v___f_5159_);
lean_closure_set(v___y_5164_, 6, v_g_5151_);
v___x_5165_ = 1;
v___x_5166_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5164_, v___x_5165_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5167_, lean_object* v_pat_5168_, lean_object* v_g_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5167_, v_pat_5168_, v_g_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5182_, lean_object* v_g_5183_, lean_object* v_pat_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l_Lean_Elab_Term_elabType(v_ty_5182_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc_n(v_a_5193_, 2);
lean_dec_ref_known(v___x_5192_, 1);
v___x_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5194_, 0, v_a_5193_);
v___x_5195_ = 0;
v___x_5196_ = lean_box(0);
v___x_5197_ = l_Lean_Meta_mkFreshExprMVar(v___x_5194_, v___x_5195_, v___x_5196_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v___y_5200_; lean_object* v___x_5254_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5197_, 1);
v___x_5254_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5184_);
if (lean_obj_tag(v___x_5254_) == 0)
{
v___y_5200_ = v___x_5196_;
goto v___jp_5199_;
}
else
{
lean_object* v_val_5255_; 
v_val_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_val_5255_);
lean_dec_ref_known(v___x_5254_, 1);
v___y_5200_ = v_val_5255_;
goto v___jp_5199_;
}
v___jp_5199_:
{
lean_object* v___x_5201_; 
lean_inc(v_a_5198_);
v___x_5201_ = l_Lean_MVarId_assert(v_g_5183_, v___y_5200_, v_a_5193_, v_a_5198_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref_known(v___x_5201_, 1);
v___x_5203_ = 0;
v___x_5204_ = l_Lean_Meta_intro1Core(v_a_5202_, v___x_5203_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v_fst_5206_; lean_object* v_snd_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5237_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref_known(v___x_5204_, 1);
v_fst_5206_ = lean_ctor_get(v_a_5205_, 0);
v_snd_5207_ = lean_ctor_get(v_a_5205_, 1);
v_isSharedCheck_5237_ = !lean_is_exclusive(v_a_5205_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5209_ = v_a_5205_;
v_isShared_5210_ = v_isSharedCheck_5237_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_snd_5207_);
lean_inc(v_fst_5206_);
lean_dec(v_a_5205_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5237_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5211_ = lean_box(0);
v___x_5212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5213_ = l_Lean_Expr_fvar___override(v_fst_5206_);
v___x_5214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5215_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5207_, v___x_5211_, v___x_5212_, v___x_5213_, v___x_5212_, v_pat_5184_, v___x_5214_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec_ref(v___x_5213_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5228_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5218_ = v___x_5215_;
v_isShared_5219_ = v_isSharedCheck_5228_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5215_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5228_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5223_; 
v___x_5220_ = l_Lean_Expr_mvarId_x21(v_a_5198_);
lean_dec(v_a_5198_);
v___x_5221_ = lean_array_to_list(v_a_5216_);
if (v_isShared_5210_ == 0)
{
lean_ctor_set_tag(v___x_5209_, 1);
lean_ctor_set(v___x_5209_, 1, v___x_5221_);
lean_ctor_set(v___x_5209_, 0, v___x_5220_);
v___x_5223_ = v___x_5209_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v___x_5221_);
v___x_5223_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
lean_object* v___x_5225_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 0, v___x_5223_);
v___x_5225_ = v___x_5218_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5236_; 
lean_del_object(v___x_5209_);
lean_dec(v_a_5198_);
v_a_5229_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5215_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5215_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5234_; 
if (v_isShared_5232_ == 0)
{
v___x_5234_ = v___x_5231_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec(v_a_5198_);
lean_dec_ref(v_pat_5184_);
v_a_5238_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5204_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5204_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
lean_dec(v_a_5198_);
lean_dec_ref(v_pat_5184_);
v_a_5246_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5201_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5201_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
lean_dec(v_a_5193_);
lean_dec_ref(v_pat_5184_);
lean_dec(v_g_5183_);
v_a_5256_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5197_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5197_);
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
else
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5271_; 
lean_dec_ref(v_pat_5184_);
lean_dec(v_g_5183_);
v_a_5264_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5266_ = v___x_5192_;
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_5192_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5269_; 
if (v_isShared_5267_ == 0)
{
v___x_5269_ = v___x_5266_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_a_5264_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5272_, lean_object* v_g_5273_, lean_object* v_pat_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5272_, v_g_5273_, v_pat_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5283_, lean_object* v_ty_5284_, lean_object* v_g_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
lean_object* v___f_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; 
v___f_5293_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5293_, 0, v_ty_5284_);
lean_closure_set(v___f_5293_, 1, v_g_5285_);
lean_closure_set(v___f_5293_, 2, v_pat_5283_);
v___x_5294_ = 1;
v___x_5295_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5293_, v___x_5294_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5296_, lean_object* v_ty_5297_, lean_object* v_g_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5296_, v_ty_5297_, v_g_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_);
lean_dec(v_a_5304_);
lean_dec_ref(v_a_5303_);
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5317_, lean_object* v_acc_5318_, lean_object* v_ty_x3f_5319_){
_start:
{
lean_object* v___x_5320_; uint8_t v___x_5321_; 
v___x_5320_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5317_);
v___x_5321_ = l_Lean_Syntax_isOfKind(v_pat_5317_, v___x_5320_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; uint8_t v___x_5323_; 
v___x_5322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5317_);
v___x_5323_ = l_Lean_Syntax_isOfKind(v_pat_5317_, v___x_5322_);
if (v___x_5323_ == 0)
{
lean_dec(v_ty_x3f_5319_);
lean_dec(v_pat_5317_);
return v_acc_5318_;
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; uint8_t v___x_5328_; 
v___x_5324_ = lean_unsigned_to_nat(1u);
v___x_5325_ = l_Lean_Syntax_getArg(v_pat_5317_, v___x_5324_);
v___x_5326_ = lean_unsigned_to_nat(2u);
v___x_5327_ = l_Lean_Syntax_getArg(v_pat_5317_, v___x_5326_);
lean_dec(v_pat_5317_);
v___x_5328_ = l_Lean_Syntax_isNone(v___x_5327_);
if (v___x_5328_ == 0)
{
uint8_t v___x_5329_; 
lean_dec(v_ty_x3f_5319_);
lean_inc(v___x_5327_);
v___x_5329_ = l_Lean_Syntax_matchesNull(v___x_5327_, v___x_5326_);
if (v___x_5329_ == 0)
{
lean_dec(v___x_5327_);
lean_dec(v___x_5325_);
return v_acc_5318_;
}
else
{
lean_object* v_ty_x3f_x27_5330_; lean_object* v___x_5331_; lean_object* v_pats_5332_; lean_object* v___x_5333_; 
v_ty_x3f_x27_5330_ = l_Lean_Syntax_getArg(v___x_5327_, v___x_5324_);
lean_dec(v___x_5327_);
v___x_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5331_, 0, v_ty_x3f_x27_5330_);
v_pats_5332_ = l_Lean_Syntax_getArgs(v___x_5325_);
lean_dec(v___x_5325_);
v___x_5333_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5332_, v_acc_5318_, v___x_5331_);
lean_dec_ref(v_pats_5332_);
return v___x_5333_;
}
}
else
{
lean_object* v_pats_5334_; lean_object* v___x_5335_; 
lean_dec(v___x_5327_);
v_pats_5334_ = l_Lean_Syntax_getArgs(v___x_5325_);
lean_dec(v___x_5325_);
v___x_5335_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5334_, v_acc_5318_, v_ty_x3f_5319_);
lean_dec_ref(v_pats_5334_);
return v___x_5335_;
}
}
}
else
{
lean_object* v___x_5336_; lean_object* v_p_5337_; 
v___x_5336_ = lean_unsigned_to_nat(0u);
v_p_5337_ = l_Lean_Syntax_getArg(v_pat_5317_, v___x_5336_);
lean_dec(v_pat_5317_);
if (lean_obj_tag(v_ty_x3f_5319_) == 0)
{
lean_object* v___x_5338_; 
v___x_5338_ = lean_array_push(v_acc_5318_, v_p_5337_);
return v___x_5338_;
}
else
{
lean_object* v_val_5339_; lean_object* v___x_5340_; lean_object* v_ref_5341_; uint8_t v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v_val_5339_ = lean_ctor_get(v_ty_x3f_5319_, 0);
lean_inc(v_val_5339_);
lean_dec_ref_known(v_ty_x3f_5319_, 1);
v___x_5340_ = lean_box(0);
v_ref_5341_ = l_Lean_replaceRef(v_p_5337_, v___x_5340_);
v___x_5342_ = 0;
v___x_5343_ = l_Lean_SourceInfo_fromRef(v_ref_5341_, v___x_5342_);
lean_dec(v_ref_5341_);
v___x_5344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5343_, 7);
v___x_5346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5346_, 0, v___x_5343_);
lean_ctor_set(v___x_5346_, 1, v___x_5345_);
v___x_5347_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5348_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5349_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5350_ = l_Lean_Syntax_node1(v___x_5343_, v___x_5349_, v_p_5337_);
v___x_5351_ = l_Lean_Syntax_node1(v___x_5343_, v___x_5348_, v___x_5350_);
v___x_5352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5343_);
lean_ctor_set(v___x_5353_, 1, v___x_5352_);
v___x_5354_ = l_Lean_Syntax_node2(v___x_5343_, v___x_5349_, v___x_5353_, v_val_5339_);
v___x_5355_ = l_Lean_Syntax_node2(v___x_5343_, v___x_5347_, v___x_5351_, v___x_5354_);
v___x_5356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5343_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
v___x_5358_ = l_Lean_Syntax_node3(v___x_5343_, v___x_5344_, v___x_5346_, v___x_5355_, v___x_5357_);
v___x_5359_ = lean_array_push(v_acc_5318_, v___x_5358_);
return v___x_5359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5360_, lean_object* v_as_5361_, size_t v_i_5362_, size_t v_stop_5363_, lean_object* v_b_5364_){
_start:
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_usize_dec_eq(v_i_5362_, v_stop_5363_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5367_; size_t v___x_5368_; size_t v___x_5369_; 
v___x_5366_ = lean_array_uget_borrowed(v_as_5361_, v_i_5362_);
lean_inc(v_ty_x3f_5360_);
lean_inc(v___x_5366_);
v___x_5367_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5366_, v_b_5364_, v_ty_x3f_5360_);
v___x_5368_ = ((size_t)1ULL);
v___x_5369_ = lean_usize_add(v_i_5362_, v___x_5368_);
v_i_5362_ = v___x_5369_;
v_b_5364_ = v___x_5367_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5360_);
return v_b_5364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5371_, lean_object* v_acc_5372_, lean_object* v_ty_x3f_5373_){
_start:
{
lean_object* v___x_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v___x_5374_ = lean_unsigned_to_nat(0u);
v___x_5375_ = lean_array_get_size(v_pats_5371_);
v___x_5376_ = lean_nat_dec_lt(v___x_5374_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_dec(v_ty_x3f_5373_);
return v_acc_5372_;
}
else
{
size_t v___x_5377_; size_t v___x_5378_; lean_object* v___x_5379_; 
v___x_5377_ = ((size_t)0ULL);
v___x_5378_ = lean_usize_of_nat(v___x_5375_);
v___x_5379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5373_, v_pats_5371_, v___x_5377_, v___x_5378_, v_acc_5372_);
return v___x_5379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5380_, lean_object* v_acc_5381_, lean_object* v_ty_x3f_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5380_, v_acc_5381_, v_ty_x3f_5382_);
lean_dec_ref(v_pats_5380_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5384_, lean_object* v_as_5385_, lean_object* v_i_5386_, lean_object* v_stop_5387_, lean_object* v_b_5388_){
_start:
{
size_t v_i_boxed_5389_; size_t v_stop_boxed_5390_; lean_object* v_res_5391_; 
v_i_boxed_5389_ = lean_unbox_usize(v_i_5386_);
lean_dec(v_i_5386_);
v_stop_boxed_5390_ = lean_unbox_usize(v_stop_5387_);
lean_dec(v_stop_5387_);
v_res_5391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5384_, v_as_5385_, v_i_boxed_5389_, v_stop_boxed_5390_, v_b_5388_);
lean_dec_ref(v_as_5385_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5393_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5394_, 0, v___x_5393_);
return v___x_5394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5397_, lean_object* v_pats_5398_, lean_object* v_ty_x3f_5399_, lean_object* v_cont_5400_, lean_object* v_i_5401_, lean_object* v_g_5402_, lean_object* v_fs_5403_, lean_object* v_clears_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5397_, v_pats_5398_, v_ty_x3f_5399_, v_cont_5400_, v_i_5401_, v_g_5402_, v_fs_5403_, v_clears_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
lean_dec(v_a_5411_);
lean_dec_ref(v_a_5410_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
lean_dec(v_i_5401_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5414_ = _args[0];
lean_object* v_ref_5415_ = _args[1];
lean_object* v_pats_5416_ = _args[2];
lean_object* v_ty_x3f_5417_ = _args[3];
lean_object* v_cont_5418_ = _args[4];
lean_object* v_i_5419_ = _args[5];
lean_object* v_g_5420_ = _args[6];
lean_object* v_fs_5421_ = _args[7];
lean_object* v_clears_5422_ = _args[8];
lean_object* v_a_5423_ = _args[9];
lean_object* v_a_5424_ = _args[10];
lean_object* v_a_5425_ = _args[11];
lean_object* v_a_5426_ = _args[12];
lean_object* v_a_5427_ = _args[13];
lean_object* v_a_5428_ = _args[14];
lean_object* v_a_5429_ = _args[15];
lean_object* v_a_5430_ = _args[16];
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5414_, v_ref_5415_, v_pats_5416_, v_ty_x3f_5417_, v_cont_5418_, v_i_5419_, v_g_5420_, v_fs_5421_, v_clears_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
lean_dec(v_a_5429_);
lean_dec_ref(v_a_5428_);
lean_dec(v_a_5427_);
lean_dec_ref(v_a_5426_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec(v_i_5419_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5432_, lean_object* v_fs_5433_, lean_object* v_clears_5434_, lean_object* v_ref_5435_, lean_object* v_pats_5436_, lean_object* v_ty_x3f_5437_, lean_object* v_a_5438_, lean_object* v_cont_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___x_5447_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5432_);
v___x_5448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5448_, 0, lean_box(0));
lean_closure_set(v___x_5448_, 1, v_ref_5435_);
lean_closure_set(v___x_5448_, 2, v_pats_5436_);
lean_closure_set(v___x_5448_, 3, v_ty_x3f_5437_);
lean_closure_set(v___x_5448_, 4, v_cont_5439_);
lean_closure_set(v___x_5448_, 5, v___x_5447_);
lean_closure_set(v___x_5448_, 6, v_g_5432_);
lean_closure_set(v___x_5448_, 7, v_fs_5433_);
lean_closure_set(v___x_5448_, 8, v_clears_5434_);
lean_closure_set(v___x_5448_, 9, v_a_5438_);
v___x_5449_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5432_, v___x_5448_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5450_, lean_object* v_fs_5451_, lean_object* v_clears_5452_, lean_object* v_a_5453_, lean_object* v_ref_5454_, lean_object* v_pat_5455_, lean_object* v_ty_x3f_5456_, lean_object* v_cont_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5470_; lean_object* v___y_5471_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5474_; lean_object* v___x_5477_; uint8_t v___x_5478_; 
v___x_5477_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5455_);
v___x_5478_ = l_Lean_Syntax_isOfKind(v_pat_5455_, v___x_5477_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; uint8_t v___x_5480_; 
lean_dec(v_ref_5454_);
v___x_5479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5455_);
v___x_5480_ = l_Lean_Syntax_isOfKind(v_pat_5455_, v___x_5479_);
if (v___x_5480_ == 0)
{
lean_object* v___x_5481_; 
lean_dec_ref(v_cont_5457_);
lean_dec(v_ty_x3f_5456_);
lean_dec(v_pat_5455_);
lean_dec(v_a_5453_);
lean_dec_ref(v_clears_5452_);
lean_dec(v_fs_5451_);
lean_dec(v_g_5450_);
v___x_5481_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5481_;
}
else
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v_ty_x3f_x27_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; 
v___x_5482_ = lean_unsigned_to_nat(1u);
v___x_5483_ = l_Lean_Syntax_getArg(v_pat_5455_, v___x_5482_);
v___x_5496_ = lean_unsigned_to_nat(2u);
v___x_5497_ = l_Lean_Syntax_getArg(v_pat_5455_, v___x_5496_);
v___x_5498_ = l_Lean_Syntax_isNone(v___x_5497_);
if (v___x_5498_ == 0)
{
uint8_t v___x_5499_; 
lean_inc(v___x_5497_);
v___x_5499_ = l_Lean_Syntax_matchesNull(v___x_5497_, v___x_5496_);
if (v___x_5499_ == 0)
{
lean_object* v___x_5500_; 
lean_dec(v___x_5497_);
lean_dec(v___x_5483_);
lean_dec_ref(v_cont_5457_);
lean_dec(v_ty_x3f_5456_);
lean_dec(v_pat_5455_);
lean_dec(v_a_5453_);
lean_dec_ref(v_clears_5452_);
lean_dec(v_fs_5451_);
lean_dec(v_g_5450_);
v___x_5500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5500_;
}
else
{
lean_object* v_ty_x3f_x27_5501_; lean_object* v___x_5502_; 
v_ty_x3f_x27_5501_ = l_Lean_Syntax_getArg(v___x_5497_, v___x_5482_);
lean_dec(v___x_5497_);
v___x_5502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5502_, 0, v_ty_x3f_x27_5501_);
v_ty_x3f_x27_5485_ = v___x_5502_;
v___y_5486_ = v_a_5458_;
v___y_5487_ = v_a_5459_;
v___y_5488_ = v_a_5460_;
v___y_5489_ = v_a_5461_;
v___y_5490_ = v_a_5462_;
v___y_5491_ = v_a_5463_;
goto v___jp_5484_;
}
}
else
{
lean_object* v___x_5503_; 
lean_dec(v___x_5497_);
v___x_5503_ = lean_box(0);
v_ty_x3f_x27_5485_ = v___x_5503_;
v___y_5486_ = v_a_5458_;
v___y_5487_ = v_a_5459_;
v___y_5488_ = v_a_5460_;
v___y_5489_ = v_a_5461_;
v___y_5490_ = v_a_5462_;
v___y_5491_ = v_a_5463_;
goto v___jp_5484_;
}
v___jp_5484_:
{
lean_object* v_pats_5492_; lean_object* v___x_5493_; uint8_t v___x_5494_; 
v_pats_5492_ = l_Lean_Syntax_getArgs(v___x_5483_);
lean_dec(v___x_5483_);
v___x_5493_ = lean_array_get_size(v_pats_5492_);
v___x_5494_ = lean_nat_dec_eq(v___x_5493_, v___x_5482_);
if (v___x_5494_ == 0)
{
lean_object* v___x_5495_; 
lean_dec(v_pat_5455_);
v___x_5495_ = lean_box(0);
v___y_5466_ = v_pats_5492_;
v___y_5467_ = v_ty_x3f_x27_5485_;
v___y_5468_ = v___y_5489_;
v___y_5469_ = v___y_5487_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v___y_5490_;
v___y_5472_ = v___y_5491_;
v___y_5473_ = v___y_5488_;
v___y_5474_ = v___x_5495_;
goto v___jp_5465_;
}
else
{
v___y_5466_ = v_pats_5492_;
v___y_5467_ = v_ty_x3f_x27_5485_;
v___y_5468_ = v___y_5489_;
v___y_5469_ = v___y_5487_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v___y_5490_;
v___y_5472_ = v___y_5491_;
v___y_5473_ = v___y_5488_;
v___y_5474_ = v_pat_5455_;
goto v___jp_5465_;
}
}
}
}
else
{
lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5504_ = lean_unsigned_to_nat(0u);
v___x_5505_ = l_Lean_Syntax_getArg(v_pat_5455_, v___x_5504_);
lean_dec(v_pat_5455_);
v___x_5506_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5505_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v_a_5507_; lean_object* v___x_5508_; lean_object* v___y_5510_; lean_object* v___y_5511_; lean_object* v___y_5535_; lean_object* v_ref_5539_; 
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
lean_inc(v_a_5507_);
lean_dec_ref_known(v___x_5506_, 1);
v___x_5508_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5454_, v_a_5507_, v_ty_x3f_5456_);
lean_dec(v_ty_x3f_5456_);
v_ref_5539_ = lean_ctor_get(v___x_5508_, 0);
lean_inc(v_ref_5539_);
v___y_5535_ = v_ref_5539_;
goto v___jp_5534_;
v___jp_5509_:
{
lean_object* v_toCold_5512_; lean_object* v_currRecDepth_5513_; lean_object* v_ref_5514_; uint16_t v_optionFlags_5515_; uint8_t v_suppressElabErrors_5516_; uint8_t v_isRecordingDeps_5517_; lean_object* v_ref_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; 
v_toCold_5512_ = lean_ctor_get(v_a_5462_, 0);
v_currRecDepth_5513_ = lean_ctor_get(v_a_5462_, 1);
v_ref_5514_ = lean_ctor_get(v_a_5462_, 2);
v_optionFlags_5515_ = lean_ctor_get_uint16(v_a_5462_, sizeof(void*)*3);
v_suppressElabErrors_5516_ = lean_ctor_get_uint8(v_a_5462_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5517_ = lean_ctor_get_uint8(v_a_5462_, sizeof(void*)*3 + 3);
v_ref_5518_ = l_Lean_replaceRef(v___y_5510_, v_ref_5514_);
lean_dec(v___y_5510_);
lean_inc(v_currRecDepth_5513_);
lean_inc_ref(v_toCold_5512_);
v___x_5519_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5519_, 0, v_toCold_5512_);
lean_ctor_set(v___x_5519_, 1, v_currRecDepth_5513_);
lean_ctor_set(v___x_5519_, 2, v_ref_5518_);
lean_ctor_set_uint16(v___x_5519_, sizeof(void*)*3, v_optionFlags_5515_);
lean_ctor_set_uint8(v___x_5519_, sizeof(void*)*3 + 2, v_suppressElabErrors_5516_);
lean_ctor_set_uint8(v___x_5519_, sizeof(void*)*3 + 3, v_isRecordingDeps_5517_);
v___x_5520_ = l_Lean_MVarId_intro(v_g_5450_, v___y_5511_, v_a_5460_, v_a_5461_, v___x_5519_, v_a_5463_);
lean_dec_ref_known(v___x_5519_, 3);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v_fst_5522_; lean_object* v_snd_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v___x_5520_, 1);
v_fst_5522_ = lean_ctor_get(v_a_5521_, 0);
lean_inc(v_fst_5522_);
v_snd_5523_ = lean_ctor_get(v_a_5521_, 1);
lean_inc(v_snd_5523_);
lean_dec(v_a_5521_);
v___x_5524_ = l_Lean_Expr_fvar___override(v_fst_5522_);
v___x_5525_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5523_, v_fs_5451_, v_clears_5452_, v___x_5524_, v_a_5453_, v___x_5508_, v_cont_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
lean_dec_ref(v___x_5524_);
return v___x_5525_;
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec_ref(v___x_5508_);
lean_dec_ref(v_cont_5457_);
lean_dec(v_a_5453_);
lean_dec_ref(v_clears_5452_);
lean_dec(v_fs_5451_);
v_a_5526_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5520_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5520_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
v___jp_5534_:
{
lean_object* v___x_5536_; 
v___x_5536_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5508_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v___x_5537_; 
v___x_5537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5510_ = v___y_5535_;
v___y_5511_ = v___x_5537_;
goto v___jp_5509_;
}
else
{
lean_object* v_val_5538_; 
v_val_5538_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_val_5538_);
lean_dec_ref_known(v___x_5536_, 1);
v___y_5510_ = v___y_5535_;
v___y_5511_ = v_val_5538_;
goto v___jp_5509_;
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec_ref(v_cont_5457_);
lean_dec(v_ty_x3f_5456_);
lean_dec(v_ref_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v_clears_5452_);
lean_dec(v_fs_5451_);
lean_dec(v_g_5450_);
v_a_5540_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5506_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5506_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
v___jp_5465_:
{
if (lean_obj_tag(v___y_5467_) == 0)
{
lean_object* v___x_5475_; 
v___x_5475_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5450_, v_fs_5451_, v_clears_5452_, v___y_5474_, v___y_5466_, v_ty_x3f_5456_, v_a_5453_, v_cont_5457_, v___y_5470_, v___y_5469_, v___y_5473_, v___y_5468_, v___y_5471_, v___y_5472_);
return v___x_5475_;
}
else
{
lean_object* v___x_5476_; 
lean_dec(v_ty_x3f_5456_);
v___x_5476_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5450_, v_fs_5451_, v_clears_5452_, v___y_5474_, v___y_5466_, v___y_5467_, v_a_5453_, v_cont_5457_, v___y_5470_, v___y_5469_, v___y_5473_, v___y_5468_, v___y_5471_, v___y_5472_);
return v___x_5476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5548_, lean_object* v_pats_5549_, lean_object* v_ty_x3f_5550_, lean_object* v_cont_5551_, lean_object* v_i_5552_, lean_object* v_g_5553_, lean_object* v_fs_5554_, lean_object* v_clears_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_){
_start:
{
lean_object* v___x_5564_; uint8_t v___x_5565_; 
v___x_5564_ = lean_array_get_size(v_pats_5549_);
v___x_5565_ = lean_nat_dec_lt(v_i_5552_, v___x_5564_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; 
lean_dec(v_ty_x3f_5550_);
lean_dec_ref(v_pats_5549_);
lean_dec(v_ref_5548_);
lean_inc(v_a_5562_);
lean_inc_ref(v_a_5561_);
lean_inc(v_a_5560_);
lean_inc_ref(v_a_5559_);
lean_inc(v_a_5558_);
lean_inc_ref(v_a_5557_);
v___x_5566_ = lean_apply_11(v_cont_5551_, v_g_5553_, v_fs_5554_, v_clears_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, lean_box(0));
return v___x_5566_;
}
else
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5567_ = lean_array_fget(v_pats_5549_, v_i_5552_);
v___x_5568_ = lean_unsigned_to_nat(1u);
v___x_5569_ = lean_nat_add(v_i_5552_, v___x_5568_);
lean_inc(v_ty_x3f_5550_);
lean_inc(v_ref_5548_);
v___x_5570_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5570_, 0, v_ref_5548_);
lean_closure_set(v___x_5570_, 1, v_pats_5549_);
lean_closure_set(v___x_5570_, 2, v_ty_x3f_5550_);
lean_closure_set(v___x_5570_, 3, v_cont_5551_);
lean_closure_set(v___x_5570_, 4, v___x_5569_);
v___x_5571_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5553_, v_fs_5554_, v_clears_5555_, v_a_5556_, v_ref_5548_, v___x_5567_, v_ty_x3f_5550_, v___x_5570_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_);
return v___x_5571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5572_, lean_object* v_ref_5573_, lean_object* v_pats_5574_, lean_object* v_ty_x3f_5575_, lean_object* v_cont_5576_, lean_object* v_i_5577_, lean_object* v_g_5578_, lean_object* v_fs_5579_, lean_object* v_clears_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_){
_start:
{
lean_object* v___x_5589_; 
v___x_5589_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5573_, v_pats_5574_, v_ty_x3f_5575_, v_cont_5576_, v_i_5577_, v_g_5578_, v_fs_5579_, v_clears_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5590_, lean_object* v_fs_5591_, lean_object* v_clears_5592_, lean_object* v_ref_5593_, lean_object* v_pats_5594_, lean_object* v_ty_x3f_5595_, lean_object* v_a_5596_, lean_object* v_cont_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_){
_start:
{
lean_object* v_res_5605_; 
v_res_5605_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5590_, v_fs_5591_, v_clears_5592_, v_ref_5593_, v_pats_5594_, v_ty_x3f_5595_, v_a_5596_, v_cont_5597_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_, v_a_5603_);
lean_dec(v_a_5603_);
lean_dec_ref(v_a_5602_);
lean_dec(v_a_5601_);
lean_dec_ref(v_a_5600_);
lean_dec(v_a_5599_);
lean_dec_ref(v_a_5598_);
return v_res_5605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5606_, lean_object* v_fs_5607_, lean_object* v_clears_5608_, lean_object* v_a_5609_, lean_object* v_ref_5610_, lean_object* v_pat_5611_, lean_object* v_ty_x3f_5612_, lean_object* v_cont_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5606_, v_fs_5607_, v_clears_5608_, v_a_5609_, v_ref_5610_, v_pat_5611_, v_ty_x3f_5612_, v_cont_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_);
lean_dec(v_a_5619_);
lean_dec_ref(v_a_5618_);
lean_dec(v_a_5617_);
lean_dec_ref(v_a_5616_);
lean_dec(v_a_5615_);
lean_dec_ref(v_a_5614_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
lean_object* v___x_5630_; 
v___x_5630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5640_, lean_object* v_g_5641_, lean_object* v_fs_5642_, lean_object* v_clears_5643_, lean_object* v_a_5644_, lean_object* v_ref_5645_, lean_object* v_pat_5646_, lean_object* v_ty_x3f_5647_, lean_object* v_cont_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v___x_5656_; 
v___x_5656_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5641_, v_fs_5642_, v_clears_5643_, v_a_5644_, v_ref_5645_, v_pat_5646_, v_ty_x3f_5647_, v_cont_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5657_, lean_object* v_g_5658_, lean_object* v_fs_5659_, lean_object* v_clears_5660_, lean_object* v_a_5661_, lean_object* v_ref_5662_, lean_object* v_pat_5663_, lean_object* v_ty_x3f_5664_, lean_object* v_cont_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5657_, v_g_5658_, v_fs_5659_, v_clears_5660_, v_a_5661_, v_ref_5662_, v_pat_5663_, v_ty_x3f_5664_, v_cont_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_);
lean_dec(v_a_5671_);
lean_dec_ref(v_a_5670_);
lean_dec(v_a_5669_);
lean_dec_ref(v_a_5668_);
lean_dec(v_a_5667_);
lean_dec_ref(v_a_5666_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5674_, lean_object* v_g_5675_, lean_object* v_fs_5676_, lean_object* v_clears_5677_, lean_object* v_ref_5678_, lean_object* v_pats_5679_, lean_object* v_ty_x3f_5680_, lean_object* v_a_5681_, lean_object* v_cont_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5675_, v_fs_5676_, v_clears_5677_, v_ref_5678_, v_pats_5679_, v_ty_x3f_5680_, v_a_5681_, v_cont_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5691_, lean_object* v_g_5692_, lean_object* v_fs_5693_, lean_object* v_clears_5694_, lean_object* v_ref_5695_, lean_object* v_pats_5696_, lean_object* v_ty_x3f_5697_, lean_object* v_a_5698_, lean_object* v_cont_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5691_, v_g_5692_, v_fs_5693_, v_clears_5694_, v_ref_5695_, v_pats_5696_, v_ty_x3f_5697_, v_a_5698_, v_cont_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_a_5701_);
lean_dec_ref(v_a_5700_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5708_, lean_object* v___x_5709_, lean_object* v___x_5710_, lean_object* v___x_5711_, lean_object* v_pats_5712_, lean_object* v_ty_x3f_5713_, lean_object* v___x_5714_, lean_object* v___x_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5708_, v___x_5709_, v___x_5710_, v___x_5711_, v_pats_5712_, v_ty_x3f_5713_, v___x_5714_, v___x_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v_a_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5732_; 
v_a_5724_ = lean_ctor_get(v___x_5723_, 0);
v_isSharedCheck_5732_ = !lean_is_exclusive(v___x_5723_);
if (v_isSharedCheck_5732_ == 0)
{
v___x_5726_ = v___x_5723_;
v_isShared_5727_ = v_isSharedCheck_5732_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_a_5724_);
lean_dec(v___x_5723_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5732_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5728_; lean_object* v___x_5730_; 
v___x_5728_ = lean_array_to_list(v_a_5724_);
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 0, v___x_5728_);
v___x_5730_ = v___x_5726_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v___x_5728_);
v___x_5730_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
return v___x_5730_;
}
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
v_a_5733_ = lean_ctor_get(v___x_5723_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5723_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5723_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5723_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5741_, lean_object* v___x_5742_, lean_object* v___x_5743_, lean_object* v___x_5744_, lean_object* v_pats_5745_, lean_object* v_ty_x3f_5746_, lean_object* v___x_5747_, lean_object* v___x_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v_res_5756_; 
v_res_5756_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5741_, v___x_5742_, v___x_5743_, v___x_5744_, v_pats_5745_, v_ty_x3f_5746_, v___x_5747_, v___x_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_);
lean_dec(v___y_5754_);
lean_dec_ref(v___y_5753_);
lean_dec(v___y_5752_);
lean_dec_ref(v___y_5751_);
lean_dec(v___y_5750_);
lean_dec_ref(v___y_5749_);
return v_res_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5757_, lean_object* v_ty_x3f_5758_, lean_object* v_g_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___f_5771_; uint8_t v___x_5772_; lean_object* v___x_5773_; 
v___x_5767_ = lean_box(0);
v___x_5768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5769_ = lean_box(0);
v___x_5770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5771_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5771_, 0, v_g_5759_);
lean_closure_set(v___f_5771_, 1, v___x_5767_);
lean_closure_set(v___f_5771_, 2, v___x_5768_);
lean_closure_set(v___f_5771_, 3, v___x_5769_);
lean_closure_set(v___f_5771_, 4, v_pats_5757_);
lean_closure_set(v___f_5771_, 5, v_ty_x3f_5758_);
lean_closure_set(v___f_5771_, 6, v___x_5768_);
lean_closure_set(v___f_5771_, 7, v___x_5770_);
v___x_5772_ = 1;
v___x_5773_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5771_, v___x_5772_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_);
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5774_, lean_object* v_ty_x3f_5775_, lean_object* v_g_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5774_, v_ty_x3f_5775_, v_g_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_);
lean_dec(v_a_5782_);
lean_dec_ref(v_a_5781_);
lean_dec(v_a_5780_);
lean_dec_ref(v_a_5779_);
lean_dec(v_a_5778_);
lean_dec_ref(v_a_5777_);
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5786_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_){
_start:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
lean_dec(v___y_5807_);
lean_dec_ref(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v___x_5822_; 
lean_inc(v___y_5816_);
lean_inc_ref(v___y_5815_);
lean_inc(v___y_5814_);
lean_inc_ref(v___y_5813_);
v___x_5822_ = lean_apply_9(v_x_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, lean_box(0));
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v_res_5833_; 
v_res_5833_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_);
lean_dec(v___y_5827_);
lean_dec_ref(v___y_5826_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
return v_res_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5834_, lean_object* v_x_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v___f_5845_; lean_object* v___x_5846_; 
lean_inc(v___y_5839_);
lean_inc_ref(v___y_5838_);
lean_inc(v___y_5837_);
lean_inc_ref(v___y_5836_);
v___f_5845_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5845_, 0, v_x_5835_);
lean_closure_set(v___f_5845_, 1, v___y_5836_);
lean_closure_set(v___f_5845_, 2, v___y_5837_);
lean_closure_set(v___f_5845_, 3, v___y_5838_);
lean_closure_set(v___f_5845_, 4, v___y_5839_);
v___x_5846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5834_, v___f_5845_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5846_) == 0)
{
return v___x_5846_;
}
else
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5854_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5849_ = v___x_5846_;
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5846_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5850_ == 0)
{
v___x_5852_ = v___x_5849_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_a_5847_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5855_, lean_object* v_x_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_){
_start:
{
lean_object* v_res_5866_; 
v_res_5866_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5855_, v_x_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
lean_dec(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec_ref(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5867_, lean_object* v_mvarId_5868_, lean_object* v_x_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_){
_start:
{
lean_object* v___x_5879_; 
v___x_5879_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5868_, v_x_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
return v___x_5879_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5880_, lean_object* v_mvarId_5881_, lean_object* v_x_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5880_, v_mvarId_5881_, v_x_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
lean_dec(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec(v___y_5884_);
lean_dec_ref(v___y_5883_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5893_, lean_object* v_pat_5894_, lean_object* v_a_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_){
_start:
{
lean_object* v___x_5905_; 
v___x_5905_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5893_, v_pat_5894_, v_a_5895_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5907_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
lean_inc(v_a_5906_);
lean_dec_ref_known(v___x_5905_, 1);
v___x_5907_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5906_, v___y_5897_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
return v___x_5907_;
}
else
{
lean_object* v_a_5908_; lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_5915_; 
v_a_5908_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5910_ = v___x_5905_;
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_a_5908_);
lean_dec(v___x_5905_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5913_; 
if (v_isShared_5911_ == 0)
{
v___x_5913_ = v___x_5910_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_a_5908_);
v___x_5913_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
return v___x_5913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5916_, lean_object* v_pat_5917_, lean_object* v_a_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
lean_object* v_res_5928_; 
v_res_5928_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5916_, v_pat_5917_, v_a_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec(v___y_5922_);
lean_dec_ref(v___y_5921_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5929_, size_t v_i_5930_, lean_object* v_bs_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_){
_start:
{
uint8_t v___x_5936_; 
v___x_5936_ = lean_usize_dec_lt(v_i_5930_, v_sz_5929_);
if (v___x_5936_ == 0)
{
lean_object* v___x_5937_; 
v___x_5937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_bs_5931_);
return v___x_5937_;
}
else
{
lean_object* v_v_5938_; lean_object* v___x_5939_; lean_object* v_bs_x27_5940_; lean_object* v___x_5941_; 
v_v_5938_ = lean_array_uget(v_bs_5931_, v_i_5930_);
v___x_5939_ = lean_unsigned_to_nat(0u);
v_bs_x27_5940_ = lean_array_uset(v_bs_5931_, v_i_5930_, v___x_5939_);
v___x_5941_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_5938_, v___y_5932_, v___y_5933_, v___y_5934_);
if (lean_obj_tag(v___x_5941_) == 0)
{
lean_object* v_a_5942_; lean_object* v_hIdent_x3f_5943_; lean_object* v_term_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5955_; 
v_a_5942_ = lean_ctor_get(v___x_5941_, 0);
lean_inc(v_a_5942_);
lean_dec_ref_known(v___x_5941_, 1);
v_hIdent_x3f_5943_ = lean_ctor_get(v_a_5942_, 0);
v_term_5944_ = lean_ctor_get(v_a_5942_, 1);
v_isSharedCheck_5955_ = !lean_is_exclusive(v_a_5942_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5946_ = v_a_5942_;
v_isShared_5947_ = v_isSharedCheck_5955_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_term_5944_);
lean_inc(v_hIdent_x3f_5943_);
lean_dec(v_a_5942_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5955_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v___x_5949_; 
if (v_isShared_5947_ == 0)
{
v___x_5949_ = v___x_5946_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_hIdent_x3f_5943_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v_term_5944_);
v___x_5949_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
size_t v___x_5950_; size_t v___x_5951_; lean_object* v___x_5952_; 
v___x_5950_ = ((size_t)1ULL);
v___x_5951_ = lean_usize_add(v_i_5930_, v___x_5950_);
v___x_5952_ = lean_array_uset(v_bs_x27_5940_, v_i_5930_, v___x_5949_);
v_i_5930_ = v___x_5951_;
v_bs_5931_ = v___x_5952_;
goto _start;
}
}
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5963_; 
lean_dec_ref(v_bs_x27_5940_);
v_a_5956_ = lean_ctor_get(v___x_5941_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5941_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5958_ = v___x_5941_;
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5941_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_5964_, lean_object* v_i_5965_, lean_object* v_bs_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_){
_start:
{
size_t v_sz_boxed_5971_; size_t v_i_boxed_5972_; lean_object* v_res_5973_; 
v_sz_boxed_5971_ = lean_unbox_usize(v_sz_5964_);
lean_dec(v_sz_5964_);
v_i_boxed_5972_ = lean_unbox_usize(v_i_5965_);
lean_dec(v_i_5965_);
v_res_5973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_5971_, v_i_boxed_5972_, v_bs_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
lean_dec(v___y_5969_);
lean_dec_ref(v___y_5968_);
lean_dec_ref(v___y_5967_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_){
_start:
{
lean_object* v___y_5991_; lean_object* v_pat_5992_; lean_object* v___y_5993_; lean_object* v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; lean_object* v___y_5997_; lean_object* v___y_5998_; lean_object* v___y_5999_; lean_object* v___y_6000_; lean_object* v___x_6026_; uint8_t v___x_6027_; 
v___x_6026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_5980_);
v___x_6027_ = l_Lean_Syntax_isOfKind(v_stx_5980_, v___x_6026_);
if (v___x_6027_ == 0)
{
lean_object* v___x_6028_; 
lean_dec(v_stx_5980_);
v___x_6028_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6028_;
}
else
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; uint8_t v___x_6033_; 
v___x_6029_ = lean_unsigned_to_nat(1u);
v___x_6030_ = l_Lean_Syntax_getArg(v_stx_5980_, v___x_6029_);
v___x_6031_ = lean_unsigned_to_nat(2u);
v___x_6032_ = l_Lean_Syntax_getArg(v_stx_5980_, v___x_6031_);
v___x_6033_ = l_Lean_Syntax_isNone(v___x_6032_);
if (v___x_6033_ == 0)
{
uint8_t v___x_6034_; 
lean_dec(v_stx_5980_);
lean_inc(v___x_6032_);
v___x_6034_ = l_Lean_Syntax_matchesNull(v___x_6032_, v___x_6031_);
if (v___x_6034_ == 0)
{
lean_object* v___x_6035_; 
lean_dec(v___x_6032_);
lean_dec(v___x_6030_);
v___x_6035_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6035_;
}
else
{
lean_object* v_pat_x3f_6036_; lean_object* v_tgts_6037_; lean_object* v___x_6038_; 
v_pat_x3f_6036_ = l_Lean_Syntax_getArg(v___x_6032_, v___x_6029_);
lean_dec(v___x_6032_);
v_tgts_6037_ = l_Lean_Syntax_getArgs(v___x_6030_);
lean_dec(v___x_6030_);
v___x_6038_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6036_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6039_);
lean_dec_ref_known(v___x_6038_, 1);
v___y_5991_ = v_tgts_6037_;
v_pat_5992_ = v_a_6039_;
v___y_5993_ = v_a_5981_;
v___y_5994_ = v_a_5982_;
v___y_5995_ = v_a_5983_;
v___y_5996_ = v_a_5984_;
v___y_5997_ = v_a_5985_;
v___y_5998_ = v_a_5986_;
v___y_5999_ = v_a_5987_;
v___y_6000_ = v_a_5988_;
goto v___jp_5990_;
}
else
{
lean_object* v_a_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6047_; 
lean_dec_ref(v_tgts_6037_);
v_a_6040_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6042_ = v___x_6038_;
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_a_6040_);
lean_dec(v___x_6038_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6045_; 
if (v_isShared_6043_ == 0)
{
v___x_6045_ = v___x_6042_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
v___x_6045_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
return v___x_6045_;
}
}
}
}
}
else
{
lean_object* v___x_6048_; lean_object* v_tk_6049_; lean_object* v_tgts_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; 
lean_dec(v___x_6032_);
v___x_6048_ = lean_unsigned_to_nat(0u);
v_tk_6049_ = l_Lean_Syntax_getArg(v_stx_5980_, v___x_6048_);
lean_dec(v_stx_5980_);
v_tgts_6050_ = l_Lean_Syntax_getArgs(v___x_6030_);
lean_dec(v___x_6030_);
v___x_6051_ = lean_box(0);
v___x_6052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6052_, 0, v_tk_6049_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
v___y_5991_ = v_tgts_6050_;
v_pat_5992_ = v___x_6052_;
v___y_5993_ = v_a_5981_;
v___y_5994_ = v_a_5982_;
v___y_5995_ = v_a_5983_;
v___y_5996_ = v_a_5984_;
v___y_5997_ = v_a_5985_;
v___y_5998_ = v_a_5986_;
v___y_5999_ = v_a_5987_;
v___y_6000_ = v_a_5988_;
goto v___jp_5990_;
}
}
v___jp_5990_:
{
lean_object* v___x_6001_; size_t v_sz_6002_; size_t v___x_6003_; lean_object* v___x_6004_; 
v___x_6001_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_5991_);
lean_dec_ref(v___y_5991_);
v_sz_6002_ = lean_array_size(v___x_6001_);
v___x_6003_ = ((size_t)0ULL);
v___x_6004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6002_, v___x_6003_, v___x_6001_, v___y_5997_, v___y_5999_, v___y_6000_);
if (lean_obj_tag(v___x_6004_) == 0)
{
lean_object* v_a_6005_; lean_object* v___x_6006_; 
v_a_6005_ = lean_ctor_get(v___x_6004_, 0);
lean_inc(v_a_6005_);
lean_dec_ref_known(v___x_6004_, 1);
v___x_6006_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5994_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
if (lean_obj_tag(v___x_6006_) == 0)
{
lean_object* v_a_6007_; lean_object* v___f_6008_; lean_object* v___x_6009_; 
v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
lean_inc_n(v_a_6007_, 2);
lean_dec_ref_known(v___x_6006_, 1);
v___f_6008_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6008_, 0, v_a_6005_);
lean_closure_set(v___f_6008_, 1, v_pat_5992_);
lean_closure_set(v___f_6008_, 2, v_a_6007_);
v___x_6009_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6007_, v___f_6008_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
return v___x_6009_;
}
else
{
lean_object* v_a_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6017_; 
lean_dec(v_a_6005_);
lean_dec_ref(v_pat_5992_);
v_a_6010_ = lean_ctor_get(v___x_6006_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_6006_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6012_ = v___x_6006_;
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_a_6010_);
lean_dec(v___x_6006_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6015_; 
if (v_isShared_6013_ == 0)
{
v___x_6015_ = v___x_6012_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_dec_ref(v_pat_5992_);
v_a_6018_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___x_6004_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_6004_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_);
lean_dec(v_a_6061_);
lean_dec_ref(v_a_6060_);
lean_dec(v_a_6059_);
lean_dec_ref(v_a_6058_);
lean_dec(v_a_6057_);
lean_dec_ref(v_a_6056_);
lean_dec(v_a_6055_);
lean_dec_ref(v_a_6054_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6064_, size_t v_i_6065_, lean_object* v_bs_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
lean_object* v___x_6076_; 
v___x_6076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6064_, v_i_6065_, v_bs_6066_, v___y_6071_, v___y_6073_, v___y_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6077_, lean_object* v_i_6078_, lean_object* v_bs_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
size_t v_sz_boxed_6089_; size_t v_i_boxed_6090_; lean_object* v_res_6091_; 
v_sz_boxed_6089_ = lean_unbox_usize(v_sz_6077_);
lean_dec(v_sz_6077_);
v_i_boxed_6090_ = lean_unbox_usize(v_i_6078_);
lean_dec(v_i_6078_);
v_res_6091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6089_, v_i_boxed_6090_, v_bs_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
lean_dec(v___y_6083_);
lean_dec_ref(v___y_6082_);
lean_dec(v___y_6081_);
lean_dec_ref(v___y_6080_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; 
v___x_6128_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6129_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6132_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6128_, v___x_6129_, v___x_6130_, v___x_6131_);
return v___x_6132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6133_){
_start:
{
lean_object* v_res_6134_; 
v_res_6134_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6135_, lean_object* v___x_6136_, lean_object* v_a_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_){
_start:
{
lean_object* v___x_6147_; 
v___x_6147_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6135_, v___x_6136_, v_a_6137_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_);
if (lean_obj_tag(v___x_6147_) == 0)
{
lean_object* v_a_6148_; lean_object* v___x_6149_; 
v_a_6148_ = lean_ctor_get(v___x_6147_, 0);
lean_inc(v_a_6148_);
lean_dec_ref_known(v___x_6147_, 1);
v___x_6149_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6148_, v___y_6139_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_);
return v___x_6149_;
}
else
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6157_; 
v_a_6150_ = lean_ctor_get(v___x_6147_, 0);
v_isSharedCheck_6157_ = !lean_is_exclusive(v___x_6147_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6152_ = v___x_6147_;
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6147_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6155_; 
if (v_isShared_6153_ == 0)
{
v___x_6155_ = v___x_6152_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
v___x_6155_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
return v___x_6155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6158_, lean_object* v___x_6159_, lean_object* v_a_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6158_, v___x_6159_, v_a_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec(v___y_6164_);
lean_dec_ref(v___y_6163_);
lean_dec(v___y_6162_);
lean_dec_ref(v___y_6161_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6171_, lean_object* v_val_6172_, lean_object* v_a_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
lean_object* v___x_6183_; 
v___x_6183_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6171_, v_val_6172_, v_a_6173_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_object* v_a_6184_; lean_object* v___x_6185_; 
v_a_6184_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_a_6184_);
lean_dec_ref_known(v___x_6183_, 1);
v___x_6185_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6184_, v___y_6175_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
return v___x_6185_;
}
else
{
lean_object* v_a_6186_; lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6193_; 
v_a_6186_ = lean_ctor_get(v___x_6183_, 0);
v_isSharedCheck_6193_ = !lean_is_exclusive(v___x_6183_);
if (v_isSharedCheck_6193_ == 0)
{
v___x_6188_ = v___x_6183_;
v_isShared_6189_ = v_isSharedCheck_6193_;
goto v_resetjp_6187_;
}
else
{
lean_inc(v_a_6186_);
lean_dec(v___x_6183_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6193_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6191_; 
if (v_isShared_6189_ == 0)
{
v___x_6191_ = v___x_6188_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
v___x_6191_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
return v___x_6191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6194_, lean_object* v_val_6195_, lean_object* v_a_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6194_, v_val_6195_, v_a_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6199_);
lean_dec(v___y_6198_);
lean_dec_ref(v___y_6197_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v_ref_6213_; lean_object* v___x_6214_; lean_object* v_a_6215_; lean_object* v___x_6217_; uint8_t v_isShared_6218_; uint8_t v_isSharedCheck_6223_; 
v_ref_6213_ = lean_ctor_get(v___y_6210_, 2);
v___x_6214_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
v_a_6215_ = lean_ctor_get(v___x_6214_, 0);
v_isSharedCheck_6223_ = !lean_is_exclusive(v___x_6214_);
if (v_isSharedCheck_6223_ == 0)
{
v___x_6217_ = v___x_6214_;
v_isShared_6218_ = v_isSharedCheck_6223_;
goto v_resetjp_6216_;
}
else
{
lean_inc(v_a_6215_);
lean_dec(v___x_6214_);
v___x_6217_ = lean_box(0);
v_isShared_6218_ = v_isSharedCheck_6223_;
goto v_resetjp_6216_;
}
v_resetjp_6216_:
{
lean_object* v___x_6219_; lean_object* v___x_6221_; 
lean_inc(v_ref_6213_);
v___x_6219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6219_, 0, v_ref_6213_);
lean_ctor_set(v___x_6219_, 1, v_a_6215_);
if (v_isShared_6218_ == 0)
{
lean_ctor_set_tag(v___x_6217_, 1);
lean_ctor_set(v___x_6217_, 0, v___x_6219_);
v___x_6221_ = v___x_6217_;
goto v_reusejp_6220_;
}
else
{
lean_object* v_reuseFailAlloc_6222_; 
v_reuseFailAlloc_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6222_, 0, v___x_6219_);
v___x_6221_ = v_reuseFailAlloc_6222_;
goto v_reusejp_6220_;
}
v_reusejp_6220_:
{
return v___x_6221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_){
_start:
{
lean_object* v_res_6230_; 
v_res_6230_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
return v_res_6230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6231_, size_t v_i_6232_, lean_object* v_bs_6233_){
_start:
{
uint8_t v___x_6234_; 
v___x_6234_ = lean_usize_dec_lt(v_i_6232_, v_sz_6231_);
if (v___x_6234_ == 0)
{
return v_bs_6233_;
}
else
{
lean_object* v_v_6235_; lean_object* v___x_6236_; lean_object* v_bs_x27_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; size_t v___x_6240_; size_t v___x_6241_; lean_object* v___x_6242_; 
v_v_6235_ = lean_array_uget(v_bs_6233_, v_i_6232_);
v___x_6236_ = lean_unsigned_to_nat(0u);
v_bs_x27_6237_ = lean_array_uset(v_bs_6233_, v_i_6232_, v___x_6236_);
v___x_6238_ = lean_box(0);
v___x_6239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6239_, 0, v___x_6238_);
lean_ctor_set(v___x_6239_, 1, v_v_6235_);
v___x_6240_ = ((size_t)1ULL);
v___x_6241_ = lean_usize_add(v_i_6232_, v___x_6240_);
v___x_6242_ = lean_array_uset(v_bs_x27_6237_, v_i_6232_, v___x_6239_);
v_i_6232_ = v___x_6241_;
v_bs_6233_ = v___x_6242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6244_, lean_object* v_i_6245_, lean_object* v_bs_6246_){
_start:
{
size_t v_sz_boxed_6247_; size_t v_i_boxed_6248_; lean_object* v_res_6249_; 
v_sz_boxed_6247_ = lean_unbox_usize(v_sz_6244_);
lean_dec(v_sz_6244_);
v_i_boxed_6248_ = lean_unbox_usize(v_i_6245_);
lean_dec(v_i_6245_);
v_res_6249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6247_, v_i_boxed_6248_, v_bs_6246_);
return v_res_6249_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6261_ = l_Lean_stringToMessageData(v___x_6260_);
return v___x_6261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_, lean_object* v_a_6265_, lean_object* v_a_6266_, lean_object* v_a_6267_, lean_object* v_a_6268_, lean_object* v_a_6269_, lean_object* v_a_6270_){
_start:
{
lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___y_6277_; lean_object* v___y_6278_; lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___x_6295_; uint8_t v___x_6296_; 
v___x_6295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6262_);
v___x_6296_ = l_Lean_Syntax_isOfKind(v_stx_6262_, v___x_6295_);
if (v___x_6296_ == 0)
{
lean_object* v___x_6297_; 
lean_dec(v_stx_6262_);
v___x_6297_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6297_;
}
else
{
lean_object* v___x_6298_; lean_object* v_tk_6299_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6307_; lean_object* v___y_6308_; lean_object* v___y_6309_; lean_object* v___y_6310_; lean_object* v___y_6311_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v_a_6340_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v_val_x3f_6356_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___x_6384_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v_ty_x3f_6388_; lean_object* v___y_6389_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v_pat_x3f_6407_; lean_object* v___y_6408_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___x_6424_; uint8_t v___x_6425_; 
v___x_6298_ = lean_unsigned_to_nat(0u);
v_tk_6299_ = l_Lean_Syntax_getArg(v_stx_6262_, v___x_6298_);
v___x_6384_ = lean_unsigned_to_nat(1u);
v___x_6424_ = l_Lean_Syntax_getArg(v_stx_6262_, v___x_6384_);
v___x_6425_ = l_Lean_Syntax_isNone(v___x_6424_);
if (v___x_6425_ == 0)
{
uint8_t v___x_6426_; 
lean_inc(v___x_6424_);
v___x_6426_ = l_Lean_Syntax_matchesNull(v___x_6424_, v___x_6384_);
if (v___x_6426_ == 0)
{
lean_object* v___x_6427_; 
lean_dec(v___x_6424_);
lean_dec(v_tk_6299_);
lean_dec(v_stx_6262_);
v___x_6427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6427_;
}
else
{
lean_object* v_pat_x3f_6428_; lean_object* v___x_6429_; uint8_t v___x_6430_; 
v_pat_x3f_6428_ = l_Lean_Syntax_getArg(v___x_6424_, v___x_6298_);
lean_dec(v___x_6424_);
v___x_6429_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6428_);
v___x_6430_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6428_, v___x_6429_);
if (v___x_6430_ == 0)
{
lean_object* v___x_6431_; 
lean_dec(v_pat_x3f_6428_);
lean_dec(v_tk_6299_);
lean_dec(v_stx_6262_);
v___x_6431_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6431_;
}
else
{
lean_object* v___x_6432_; 
v___x_6432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6432_, 0, v_pat_x3f_6428_);
v_pat_x3f_6407_ = v___x_6432_;
v___y_6408_ = v_a_6263_;
v___y_6409_ = v_a_6264_;
v___y_6410_ = v_a_6265_;
v___y_6411_ = v_a_6266_;
v___y_6412_ = v_a_6267_;
v___y_6413_ = v_a_6268_;
v___y_6414_ = v_a_6269_;
v___y_6415_ = v_a_6270_;
goto v___jp_6406_;
}
}
}
else
{
lean_object* v___x_6433_; 
lean_dec(v___x_6424_);
v___x_6433_ = lean_box(0);
v_pat_x3f_6407_ = v___x_6433_;
v___y_6408_ = v_a_6263_;
v___y_6409_ = v_a_6264_;
v___y_6410_ = v_a_6265_;
v___y_6411_ = v_a_6266_;
v___y_6412_ = v_a_6267_;
v___y_6413_ = v_a_6268_;
v___y_6414_ = v_a_6269_;
v___y_6415_ = v_a_6270_;
goto v___jp_6406_;
}
v___jp_6300_:
{
lean_object* v___x_6312_; lean_object* v___x_6313_; size_t v_sz_6314_; size_t v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6312_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6299_, v___y_6311_, v___y_6308_);
lean_dec(v___y_6308_);
v___x_6313_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6305_);
lean_dec_ref(v___y_6305_);
v_sz_6314_ = lean_array_size(v___x_6313_);
v___x_6315_ = ((size_t)0ULL);
v___x_6316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6314_, v___x_6315_, v___x_6313_);
v___x_6317_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6304_, v___y_6309_, v___y_6302_, v___y_6301_, v___y_6307_);
if (lean_obj_tag(v___x_6317_) == 0)
{
lean_object* v_a_6318_; lean_object* v___f_6319_; lean_object* v___x_6320_; 
v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
lean_inc_n(v_a_6318_, 2);
lean_dec_ref_known(v___x_6317_, 1);
v___f_6319_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6319_, 0, v___x_6316_);
lean_closure_set(v___f_6319_, 1, v___x_6312_);
lean_closure_set(v___f_6319_, 2, v_a_6318_);
v___x_6320_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6318_, v___f_6319_, v___y_6303_, v___y_6304_, v___y_6310_, v___y_6306_, v___y_6309_, v___y_6302_, v___y_6301_, v___y_6307_);
return v___x_6320_;
}
else
{
lean_object* v_a_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6328_; 
lean_dec_ref(v___x_6316_);
lean_dec_ref(v___x_6312_);
v_a_6321_ = lean_ctor_get(v___x_6317_, 0);
v_isSharedCheck_6328_ = !lean_is_exclusive(v___x_6317_);
if (v_isSharedCheck_6328_ == 0)
{
v___x_6323_ = v___x_6317_;
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_a_6321_);
lean_dec(v___x_6317_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v___x_6326_; 
if (v_isShared_6324_ == 0)
{
v___x_6326_ = v___x_6323_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6327_; 
v_reuseFailAlloc_6327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_a_6321_);
v___x_6326_ = v_reuseFailAlloc_6327_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
return v___x_6326_;
}
}
}
}
v___jp_6329_:
{
if (lean_obj_tag(v___y_6336_) == 1)
{
if (lean_obj_tag(v_a_6340_) == 0)
{
lean_object* v_val_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v_val_6341_ = lean_ctor_get(v___y_6336_, 0);
lean_inc(v_val_6341_);
lean_dec_ref_known(v___y_6336_, 1);
v___x_6342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6299_);
v___x_6343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6343_, 0, v_tk_6299_);
lean_ctor_set(v___x_6343_, 1, v___x_6342_);
v___y_6301_ = v___y_6331_;
v___y_6302_ = v___y_6330_;
v___y_6303_ = v___y_6332_;
v___y_6304_ = v___y_6333_;
v___y_6305_ = v_val_6341_;
v___y_6306_ = v___y_6335_;
v___y_6307_ = v___y_6334_;
v___y_6308_ = v___y_6337_;
v___y_6309_ = v___y_6338_;
v___y_6310_ = v___y_6339_;
v___y_6311_ = v___x_6343_;
goto v___jp_6300_;
}
else
{
lean_object* v_val_6344_; lean_object* v_val_6345_; 
v_val_6344_ = lean_ctor_get(v___y_6336_, 0);
lean_inc(v_val_6344_);
lean_dec_ref_known(v___y_6336_, 1);
v_val_6345_ = lean_ctor_get(v_a_6340_, 0);
lean_inc(v_val_6345_);
lean_dec_ref_known(v_a_6340_, 1);
v___y_6301_ = v___y_6331_;
v___y_6302_ = v___y_6330_;
v___y_6303_ = v___y_6332_;
v___y_6304_ = v___y_6333_;
v___y_6305_ = v_val_6344_;
v___y_6306_ = v___y_6335_;
v___y_6307_ = v___y_6334_;
v___y_6308_ = v___y_6337_;
v___y_6309_ = v___y_6338_;
v___y_6310_ = v___y_6339_;
v___y_6311_ = v_val_6345_;
goto v___jp_6300_;
}
}
else
{
lean_dec(v___y_6336_);
if (lean_obj_tag(v___y_6337_) == 1)
{
if (lean_obj_tag(v_a_6340_) == 0)
{
lean_object* v_val_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v_val_6346_ = lean_ctor_get(v___y_6337_, 0);
lean_inc(v_val_6346_);
lean_dec_ref_known(v___y_6337_, 1);
v___x_6347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6348_, 0, v_tk_6299_);
lean_ctor_set(v___x_6348_, 1, v___x_6347_);
v___y_6273_ = v_val_6346_;
v___y_6274_ = v___y_6331_;
v___y_6275_ = v___y_6330_;
v___y_6276_ = v___y_6332_;
v___y_6277_ = v___y_6333_;
v___y_6278_ = v___y_6335_;
v___y_6279_ = v___y_6334_;
v___y_6280_ = v___y_6338_;
v___y_6281_ = v___y_6339_;
v___y_6282_ = v___x_6348_;
goto v___jp_6272_;
}
else
{
lean_object* v_val_6349_; lean_object* v_val_6350_; 
lean_dec(v_tk_6299_);
v_val_6349_ = lean_ctor_get(v___y_6337_, 0);
lean_inc(v_val_6349_);
lean_dec_ref_known(v___y_6337_, 1);
v_val_6350_ = lean_ctor_get(v_a_6340_, 0);
lean_inc(v_val_6350_);
lean_dec_ref_known(v_a_6340_, 1);
v___y_6273_ = v_val_6349_;
v___y_6274_ = v___y_6331_;
v___y_6275_ = v___y_6330_;
v___y_6276_ = v___y_6332_;
v___y_6277_ = v___y_6333_;
v___y_6278_ = v___y_6335_;
v___y_6279_ = v___y_6334_;
v___y_6280_ = v___y_6338_;
v___y_6281_ = v___y_6339_;
v___y_6282_ = v_val_6350_;
goto v___jp_6272_;
}
}
else
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
lean_dec(v_a_6340_);
lean_dec(v___y_6337_);
lean_dec(v_tk_6299_);
v___x_6351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6352_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6351_, v___y_6338_, v___y_6330_, v___y_6331_, v___y_6334_);
return v___x_6352_;
}
}
}
v___jp_6353_:
{
if (lean_obj_tag(v___y_6354_) == 0)
{
lean_object* v___x_6365_; 
v___x_6365_ = lean_box(0);
v___y_6330_ = v___y_6362_;
v___y_6331_ = v___y_6363_;
v___y_6332_ = v___y_6357_;
v___y_6333_ = v___y_6358_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6360_;
v___y_6336_ = v_val_x3f_6356_;
v___y_6337_ = v___y_6355_;
v___y_6338_ = v___y_6361_;
v___y_6339_ = v___y_6359_;
v_a_6340_ = v___x_6365_;
goto v___jp_6329_;
}
else
{
lean_object* v_val_6366_; lean_object* v___x_6368_; uint8_t v_isShared_6369_; uint8_t v_isSharedCheck_6383_; 
v_val_6366_ = lean_ctor_get(v___y_6354_, 0);
v_isSharedCheck_6383_ = !lean_is_exclusive(v___y_6354_);
if (v_isSharedCheck_6383_ == 0)
{
v___x_6368_ = v___y_6354_;
v_isShared_6369_ = v_isSharedCheck_6383_;
goto v_resetjp_6367_;
}
else
{
lean_inc(v_val_6366_);
lean_dec(v___y_6354_);
v___x_6368_ = lean_box(0);
v_isShared_6369_ = v_isSharedCheck_6383_;
goto v_resetjp_6367_;
}
v_resetjp_6367_:
{
lean_object* v___x_6370_; 
v___x_6370_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6366_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; lean_object* v___x_6373_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_a_6371_);
lean_dec_ref_known(v___x_6370_, 1);
if (v_isShared_6369_ == 0)
{
lean_ctor_set(v___x_6368_, 0, v_a_6371_);
v___x_6373_ = v___x_6368_;
goto v_reusejp_6372_;
}
else
{
lean_object* v_reuseFailAlloc_6374_; 
v_reuseFailAlloc_6374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_a_6371_);
v___x_6373_ = v_reuseFailAlloc_6374_;
goto v_reusejp_6372_;
}
v_reusejp_6372_:
{
v___y_6330_ = v___y_6362_;
v___y_6331_ = v___y_6363_;
v___y_6332_ = v___y_6357_;
v___y_6333_ = v___y_6358_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6360_;
v___y_6336_ = v_val_x3f_6356_;
v___y_6337_ = v___y_6355_;
v___y_6338_ = v___y_6361_;
v___y_6339_ = v___y_6359_;
v_a_6340_ = v___x_6373_;
goto v___jp_6329_;
}
}
else
{
lean_object* v_a_6375_; lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6382_; 
lean_del_object(v___x_6368_);
lean_dec(v_val_x3f_6356_);
lean_dec(v___y_6355_);
lean_dec(v_tk_6299_);
v_a_6375_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6382_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6382_ == 0)
{
v___x_6377_ = v___x_6370_;
v_isShared_6378_ = v_isSharedCheck_6382_;
goto v_resetjp_6376_;
}
else
{
lean_inc(v_a_6375_);
lean_dec(v___x_6370_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6382_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
lean_object* v___x_6380_; 
if (v_isShared_6378_ == 0)
{
v___x_6380_ = v___x_6377_;
goto v_reusejp_6379_;
}
else
{
lean_object* v_reuseFailAlloc_6381_; 
v_reuseFailAlloc_6381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_a_6375_);
v___x_6380_ = v_reuseFailAlloc_6381_;
goto v_reusejp_6379_;
}
v_reusejp_6379_:
{
return v___x_6380_;
}
}
}
}
}
}
v___jp_6385_:
{
lean_object* v___x_6397_; lean_object* v___x_6398_; uint8_t v___x_6399_; 
v___x_6397_ = lean_unsigned_to_nat(3u);
v___x_6398_ = l_Lean_Syntax_getArg(v_stx_6262_, v___x_6397_);
lean_dec(v_stx_6262_);
v___x_6399_ = l_Lean_Syntax_isNone(v___x_6398_);
if (v___x_6399_ == 0)
{
uint8_t v___x_6400_; 
lean_inc(v___x_6398_);
v___x_6400_ = l_Lean_Syntax_matchesNull(v___x_6398_, v___y_6386_);
if (v___x_6400_ == 0)
{
lean_object* v___x_6401_; 
lean_dec(v___x_6398_);
lean_dec(v_ty_x3f_6388_);
lean_dec(v___y_6387_);
lean_dec(v_tk_6299_);
v___x_6401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6401_;
}
else
{
lean_object* v___x_6402_; lean_object* v_val_x3f_6403_; lean_object* v___x_6404_; 
v___x_6402_ = l_Lean_Syntax_getArg(v___x_6398_, v___x_6384_);
lean_dec(v___x_6398_);
v_val_x3f_6403_ = l_Lean_Syntax_getArgs(v___x_6402_);
lean_dec(v___x_6402_);
v___x_6404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6404_, 0, v_val_x3f_6403_);
v___y_6354_ = v___y_6387_;
v___y_6355_ = v_ty_x3f_6388_;
v_val_x3f_6356_ = v___x_6404_;
v___y_6357_ = v___y_6389_;
v___y_6358_ = v___y_6390_;
v___y_6359_ = v___y_6391_;
v___y_6360_ = v___y_6392_;
v___y_6361_ = v___y_6393_;
v___y_6362_ = v___y_6394_;
v___y_6363_ = v___y_6395_;
v___y_6364_ = v___y_6396_;
goto v___jp_6353_;
}
}
else
{
lean_object* v___x_6405_; 
lean_dec(v___x_6398_);
v___x_6405_ = lean_box(0);
v___y_6354_ = v___y_6387_;
v___y_6355_ = v_ty_x3f_6388_;
v_val_x3f_6356_ = v___x_6405_;
v___y_6357_ = v___y_6389_;
v___y_6358_ = v___y_6390_;
v___y_6359_ = v___y_6391_;
v___y_6360_ = v___y_6392_;
v___y_6361_ = v___y_6393_;
v___y_6362_ = v___y_6394_;
v___y_6363_ = v___y_6395_;
v___y_6364_ = v___y_6396_;
goto v___jp_6353_;
}
}
v___jp_6406_:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; uint8_t v___x_6418_; 
v___x_6416_ = lean_unsigned_to_nat(2u);
v___x_6417_ = l_Lean_Syntax_getArg(v_stx_6262_, v___x_6416_);
v___x_6418_ = l_Lean_Syntax_isNone(v___x_6417_);
if (v___x_6418_ == 0)
{
uint8_t v___x_6419_; 
lean_inc(v___x_6417_);
v___x_6419_ = l_Lean_Syntax_matchesNull(v___x_6417_, v___x_6416_);
if (v___x_6419_ == 0)
{
lean_object* v___x_6420_; 
lean_dec(v___x_6417_);
lean_dec(v_pat_x3f_6407_);
lean_dec(v_tk_6299_);
lean_dec(v_stx_6262_);
v___x_6420_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6420_;
}
else
{
lean_object* v_ty_x3f_6421_; lean_object* v___x_6422_; 
v_ty_x3f_6421_ = l_Lean_Syntax_getArg(v___x_6417_, v___x_6384_);
lean_dec(v___x_6417_);
v___x_6422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6422_, 0, v_ty_x3f_6421_);
v___y_6386_ = v___x_6416_;
v___y_6387_ = v_pat_x3f_6407_;
v_ty_x3f_6388_ = v___x_6422_;
v___y_6389_ = v___y_6408_;
v___y_6390_ = v___y_6409_;
v___y_6391_ = v___y_6410_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6412_;
v___y_6394_ = v___y_6413_;
v___y_6395_ = v___y_6414_;
v___y_6396_ = v___y_6415_;
goto v___jp_6385_;
}
}
else
{
lean_object* v___x_6423_; 
lean_dec(v___x_6417_);
v___x_6423_ = lean_box(0);
v___y_6386_ = v___x_6416_;
v___y_6387_ = v_pat_x3f_6407_;
v_ty_x3f_6388_ = v___x_6423_;
v___y_6389_ = v___y_6408_;
v___y_6390_ = v___y_6409_;
v___y_6391_ = v___y_6410_;
v___y_6392_ = v___y_6411_;
v___y_6393_ = v___y_6412_;
v___y_6394_ = v___y_6413_;
v___y_6395_ = v___y_6414_;
v___y_6396_ = v___y_6415_;
goto v___jp_6385_;
}
}
}
v___jp_6272_:
{
lean_object* v___x_6283_; 
v___x_6283_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6277_, v___y_6280_, v___y_6275_, v___y_6274_, v___y_6279_);
if (lean_obj_tag(v___x_6283_) == 0)
{
lean_object* v_a_6284_; lean_object* v___f_6285_; lean_object* v___x_6286_; 
v_a_6284_ = lean_ctor_get(v___x_6283_, 0);
lean_inc_n(v_a_6284_, 2);
lean_dec_ref_known(v___x_6283_, 1);
v___f_6285_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6285_, 0, v___y_6282_);
lean_closure_set(v___f_6285_, 1, v___y_6273_);
lean_closure_set(v___f_6285_, 2, v_a_6284_);
v___x_6286_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6284_, v___f_6285_, v___y_6276_, v___y_6277_, v___y_6281_, v___y_6278_, v___y_6280_, v___y_6275_, v___y_6274_, v___y_6279_);
return v___x_6286_;
}
else
{
lean_object* v_a_6287_; lean_object* v___x_6289_; uint8_t v_isShared_6290_; uint8_t v_isSharedCheck_6294_; 
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6273_);
v_a_6287_ = lean_ctor_get(v___x_6283_, 0);
v_isSharedCheck_6294_ = !lean_is_exclusive(v___x_6283_);
if (v_isSharedCheck_6294_ == 0)
{
v___x_6289_ = v___x_6283_;
v_isShared_6290_ = v_isSharedCheck_6294_;
goto v_resetjp_6288_;
}
else
{
lean_inc(v_a_6287_);
lean_dec(v___x_6283_);
v___x_6289_ = lean_box(0);
v_isShared_6290_ = v_isSharedCheck_6294_;
goto v_resetjp_6288_;
}
v_resetjp_6288_:
{
lean_object* v___x_6292_; 
if (v_isShared_6290_ == 0)
{
v___x_6292_ = v___x_6289_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6293_; 
v_reuseFailAlloc_6293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_a_6287_);
v___x_6292_ = v_reuseFailAlloc_6293_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
return v___x_6292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6434_, lean_object* v_a_6435_, lean_object* v_a_6436_, lean_object* v_a_6437_, lean_object* v_a_6438_, lean_object* v_a_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_){
_start:
{
lean_object* v_res_6444_; 
v_res_6444_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6434_, v_a_6435_, v_a_6436_, v_a_6437_, v_a_6438_, v_a_6439_, v_a_6440_, v_a_6441_, v_a_6442_);
lean_dec(v_a_6442_);
lean_dec_ref(v_a_6441_);
lean_dec(v_a_6440_);
lean_dec_ref(v_a_6439_);
lean_dec(v_a_6438_);
lean_dec_ref(v_a_6437_);
lean_dec(v_a_6436_);
lean_dec_ref(v_a_6435_);
return v_res_6444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6445_, lean_object* v_msg_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_){
_start:
{
lean_object* v___x_6456_; 
v___x_6456_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6446_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
return v___x_6456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6457_, lean_object* v_msg_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_){
_start:
{
lean_object* v_res_6468_; 
v_res_6468_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6457_, v_msg_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
lean_dec(v___y_6464_);
lean_dec_ref(v___y_6463_);
lean_dec(v___y_6462_);
lean_dec_ref(v___y_6461_);
lean_dec(v___y_6460_);
lean_dec_ref(v___y_6459_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6474_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6477_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6478_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6474_, v___x_6475_, v___x_6476_, v___x_6477_);
return v___x_6478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6479_){
_start:
{
lean_object* v_res_6480_; 
v_res_6480_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6481_, lean_object* v_ty_x3f_6482_, lean_object* v_a_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_){
_start:
{
lean_object* v___x_6493_; 
v___x_6493_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6481_, v_ty_x3f_6482_, v_a_6483_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
if (lean_obj_tag(v___x_6493_) == 0)
{
lean_object* v_a_6494_; lean_object* v___x_6495_; 
v_a_6494_ = lean_ctor_get(v___x_6493_, 0);
lean_inc(v_a_6494_);
lean_dec_ref_known(v___x_6493_, 1);
v___x_6495_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6494_, v___y_6485_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
return v___x_6495_;
}
else
{
lean_object* v_a_6496_; lean_object* v___x_6498_; uint8_t v_isShared_6499_; uint8_t v_isSharedCheck_6503_; 
v_a_6496_ = lean_ctor_get(v___x_6493_, 0);
v_isSharedCheck_6503_ = !lean_is_exclusive(v___x_6493_);
if (v_isSharedCheck_6503_ == 0)
{
v___x_6498_ = v___x_6493_;
v_isShared_6499_ = v_isSharedCheck_6503_;
goto v_resetjp_6497_;
}
else
{
lean_inc(v_a_6496_);
lean_dec(v___x_6493_);
v___x_6498_ = lean_box(0);
v_isShared_6499_ = v_isSharedCheck_6503_;
goto v_resetjp_6497_;
}
v_resetjp_6497_:
{
lean_object* v___x_6501_; 
if (v_isShared_6499_ == 0)
{
v___x_6501_ = v___x_6498_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_a_6496_);
v___x_6501_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
return v___x_6501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6504_, lean_object* v_ty_x3f_6505_, lean_object* v_a_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_){
_start:
{
lean_object* v_res_6516_; 
v_res_6516_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6504_, v_ty_x3f_6505_, v_a_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_);
lean_dec(v___y_6514_);
lean_dec_ref(v___y_6513_);
lean_dec(v___y_6512_);
lean_dec_ref(v___y_6511_);
lean_dec(v___y_6510_);
lean_dec_ref(v___y_6509_);
lean_dec(v___y_6508_);
lean_dec_ref(v___y_6507_);
return v_res_6516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_, lean_object* v_a_6526_, lean_object* v_a_6527_, lean_object* v_a_6528_, lean_object* v_a_6529_, lean_object* v_a_6530_, lean_object* v_a_6531_){
_start:
{
lean_object* v___x_6533_; uint8_t v___x_6534_; 
v___x_6533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6523_);
v___x_6534_ = l_Lean_Syntax_isOfKind(v_stx_6523_, v___x_6533_);
if (v___x_6534_ == 0)
{
lean_object* v___x_6535_; 
lean_dec(v_stx_6523_);
v___x_6535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6535_;
}
else
{
lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v_ty_x3f_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___x_6561_; lean_object* v___x_6562_; uint8_t v___x_6563_; 
v___x_6536_ = lean_unsigned_to_nat(1u);
v___x_6537_ = l_Lean_Syntax_getArg(v_stx_6523_, v___x_6536_);
v___x_6561_ = lean_unsigned_to_nat(2u);
v___x_6562_ = l_Lean_Syntax_getArg(v_stx_6523_, v___x_6561_);
lean_dec(v_stx_6523_);
v___x_6563_ = l_Lean_Syntax_isNone(v___x_6562_);
if (v___x_6563_ == 0)
{
uint8_t v___x_6564_; 
lean_inc(v___x_6562_);
v___x_6564_ = l_Lean_Syntax_matchesNull(v___x_6562_, v___x_6561_);
if (v___x_6564_ == 0)
{
lean_object* v___x_6565_; 
lean_dec(v___x_6562_);
lean_dec(v___x_6537_);
v___x_6565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6565_;
}
else
{
lean_object* v_ty_x3f_6566_; lean_object* v___x_6567_; 
v_ty_x3f_6566_ = l_Lean_Syntax_getArg(v___x_6562_, v___x_6536_);
lean_dec(v___x_6562_);
v___x_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6567_, 0, v_ty_x3f_6566_);
v_ty_x3f_6539_ = v___x_6567_;
v___y_6540_ = v_a_6524_;
v___y_6541_ = v_a_6525_;
v___y_6542_ = v_a_6526_;
v___y_6543_ = v_a_6527_;
v___y_6544_ = v_a_6528_;
v___y_6545_ = v_a_6529_;
v___y_6546_ = v_a_6530_;
v___y_6547_ = v_a_6531_;
goto v___jp_6538_;
}
}
else
{
lean_object* v___x_6568_; 
lean_dec(v___x_6562_);
v___x_6568_ = lean_box(0);
v_ty_x3f_6539_ = v___x_6568_;
v___y_6540_ = v_a_6524_;
v___y_6541_ = v_a_6525_;
v___y_6542_ = v_a_6526_;
v___y_6543_ = v_a_6527_;
v___y_6544_ = v_a_6528_;
v___y_6545_ = v_a_6529_;
v___y_6546_ = v_a_6530_;
v___y_6547_ = v_a_6531_;
goto v___jp_6538_;
}
v___jp_6538_:
{
lean_object* v_pats_6548_; lean_object* v___x_6549_; 
v_pats_6548_ = l_Lean_Syntax_getArgs(v___x_6537_);
lean_dec(v___x_6537_);
v___x_6549_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6541_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
if (lean_obj_tag(v___x_6549_) == 0)
{
lean_object* v_a_6550_; lean_object* v___f_6551_; lean_object* v___x_6552_; 
v_a_6550_ = lean_ctor_get(v___x_6549_, 0);
lean_inc_n(v_a_6550_, 2);
lean_dec_ref_known(v___x_6549_, 1);
v___f_6551_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6551_, 0, v_pats_6548_);
lean_closure_set(v___f_6551_, 1, v_ty_x3f_6539_);
lean_closure_set(v___f_6551_, 2, v_a_6550_);
v___x_6552_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6550_, v___f_6551_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
return v___x_6552_;
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
lean_dec_ref(v_pats_6548_);
lean_dec(v_ty_x3f_6539_);
v_a_6553_ = lean_ctor_get(v___x_6549_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6549_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6549_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6549_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_, lean_object* v_a_6578_){
_start:
{
lean_object* v_res_6579_; 
v_res_6579_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_, v_a_6574_, v_a_6575_, v_a_6576_, v_a_6577_);
lean_dec(v_a_6577_);
lean_dec_ref(v_a_6576_);
lean_dec(v_a_6575_);
lean_dec_ref(v_a_6574_);
lean_dec(v_a_6573_);
lean_dec_ref(v_a_6572_);
lean_dec(v_a_6571_);
lean_dec_ref(v_a_6570_);
return v_res_6579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6585_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6588_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6589_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6585_, v___x_6586_, v___x_6587_, v___x_6588_);
return v___x_6589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6591_;
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
