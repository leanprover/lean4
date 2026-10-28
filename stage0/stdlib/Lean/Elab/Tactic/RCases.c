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
lean_ctor_set(v___x_860_, 1, v___y_857_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_856_);
lean_ctor_set(v___x_861_, 1, v___y_858_);
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
v___y_857_ = v_fst_868_;
v___y_858_ = v_snd_869_;
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
v___y_857_ = v_fst_868_;
v___y_858_ = v_snd_869_;
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
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_969_, 10, v___x_967_);
lean_ctor_set(v___x_969_, 11, v___x_966_);
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
lean_inc_ref(v___x_1014_);
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
v___x_1023_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1014_, v_declHint_1005_);
lean_dec_ref(v___x_1014_);
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
lean_object* v_toCold_1154_; lean_object* v_currRecDepth_1155_; lean_object* v_ref_1156_; uint16_t v_optionFlags_1157_; uint8_t v_suppressElabErrors_1158_; uint8_t v_checkDeprecated_1159_; uint8_t v_isRecordingDeps_1160_; lean_object* v_ref_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_toCold_1154_ = lean_ctor_get(v___y_1151_, 0);
v_currRecDepth_1155_ = lean_ctor_get(v___y_1151_, 1);
v_ref_1156_ = lean_ctor_get(v___y_1151_, 2);
v_optionFlags_1157_ = lean_ctor_get_uint16(v___y_1151_, sizeof(void*)*3);
v_suppressElabErrors_1158_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*3 + 2);
v_checkDeprecated_1159_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1160_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*3 + 4);
v_ref_1161_ = l_Lean_replaceRef(v_ref_1147_, v_ref_1156_);
lean_inc(v_currRecDepth_1155_);
lean_inc_ref(v_toCold_1154_);
v___x_1162_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1162_, 0, v_toCold_1154_);
lean_ctor_set(v___x_1162_, 1, v_currRecDepth_1155_);
lean_ctor_set(v___x_1162_, 2, v_ref_1161_);
lean_ctor_set_uint16(v___x_1162_, sizeof(void*)*3, v_optionFlags_1157_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3 + 2, v_suppressElabErrors_1158_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3 + 3, v_checkDeprecated_1159_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3 + 4, v_isRecordingDeps_1160_);
v___x_1163_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1148_, v___y_1149_, v___y_1150_, v___x_1162_, v___y_1152_);
lean_dec_ref_known(v___x_1162_, 3);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1164_, v_msg_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v_ref_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1172_, lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_a_1181_; lean_object* v___x_1182_; 
v___x_1180_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1173_, v_declHint_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1172_, v_a_1181_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1183_, lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1183_, v_msg_1184_, v_declHint_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_ref_1183_);
return v_res_1191_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1198_, lean_object* v_constName_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1205_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1206_ = 0;
lean_inc(v_constName_1199_);
v___x_1207_ = l_Lean_MessageData_ofConstName(v_constName_1199_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1205_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1198_, v___x_1210_, v_constName_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1212_, lean_object* v_constName_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1212_, v_constName_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v_ref_1212_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_ref_1226_; lean_object* v___x_1227_; 
v_ref_1226_ = lean_ctor_get(v___y_1223_, 2);
v___x_1227_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1226_, v_constName_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object* v_constName_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_env_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = lean_st_ref_get(v___y_1239_);
v_env_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_env_1242_);
lean_dec(v___x_1241_);
v___x_1243_ = 0;
lean_inc(v_constName_1235_);
v___x_1244_ = l_Lean_Environment_findConstVal_x3f(v_env_1242_, v_constName_1235_, v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_constName_1235_);
v_val_1246_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1244_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_dec(v___x_1244_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 0);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_val_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object* v_constName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
if (lean_obj_tag(v_a_1261_) == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = l_List_reverse___redArg(v_a_1262_);
return v___x_1263_;
}
else
{
lean_object* v_head_1264_; lean_object* v_tail_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1274_; 
v_head_1264_ = lean_ctor_get(v_a_1261_, 0);
v_tail_1265_ = lean_ctor_get(v_a_1261_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_a_1261_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1267_ = v_a_1261_;
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_tail_1265_);
lean_inc(v_head_1264_);
lean_dec(v_a_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = l_Lean_mkLevelParam(v_head_1264_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_a_1262_);
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_a_1262_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v_a_1261_ = v_tail_1265_;
v_a_1262_ = v___x_1271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object* v_constName_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
lean_inc(v_constName_1275_);
v___x_1281_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1293_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_levelParams_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v_levelParams_1286_ = lean_ctor_get(v_a_1282_, 1);
lean_inc(v_levelParams_1286_);
lean_dec(v_a_1282_);
v___x_1287_ = lean_box(0);
v___x_1288_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(v_levelParams_1286_, v___x_1287_);
v___x_1289_ = l_Lean_mkConst(v_constName_1275_, v___x_1288_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1289_);
v___x_1291_ = v___x_1284_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_constName_1275_);
v_a_1294_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1281_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1281_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object* v_constName_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_constName_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object* v_ref_1309_, lean_object* v_params_1310_, lean_object* v_altVarNames_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec(v_x_1313_);
lean_dec(v_ref_1309_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_altVarNames_1311_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
else
{
lean_object* v_head_1322_; lean_object* v_tail_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1429_; 
v_head_1322_ = lean_ctor_get(v_x_1312_, 0);
v_tail_1323_ = lean_ctor_get(v_x_1312_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1312_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1325_ = v_x_1312_;
v_isShared_1326_ = v_isSharedCheck_1429_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_tail_1323_);
lean_inc(v_head_1322_);
lean_dec(v_x_1312_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1429_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; 
lean_inc(v_head_1322_);
v___x_1327_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_head_1322_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Lean_Meta_getFunInfo(v_a_1328_, v___x_1329_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_paramInfo_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1411_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v_paramInfo_1332_ = lean_ctor_get(v_a_1331_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_a_1331_, 1);
lean_dec(v_unused_1412_);
v___x_1334_ = v_a_1331_;
v_isShared_1335_ = v_isSharedCheck_1411_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_paramInfo_1332_);
lean_dec(v_a_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1411_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1376_; uint8_t v_fst_1377_; lean_object* v_snd_1378_; lean_object* v_snd_1379_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1406_; 
if (lean_obj_tag(v_x_1313_) == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_1406_ = v___x_1409_;
goto v___jp_1405_;
}
else
{
lean_object* v_head_1410_; 
v_head_1410_ = lean_ctor_get(v_x_1313_, 0);
lean_inc(v_head_1410_);
v___y_1406_ = v_head_1410_;
goto v___jp_1405_;
}
v___jp_1336_:
{
lean_object* v___x_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1374_; 
v___x_1341_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1340_, v_paramInfo_1332_, v___y_1339_, v_params_1310_, v___y_1338_);
lean_dec_ref(v_paramInfo_1332_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
v_snd_1343_ = lean_ctor_get(v___x_1341_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1345_ = v___x_1341_;
v_isShared_1346_ = v_isSharedCheck_1374_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_inc(v_fst_1342_);
lean_dec(v___x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1374_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = 1;
v___x_1348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1348_, 0, v_fst_1342_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*1, v___x_1347_);
v___x_1349_ = lean_array_push(v_altVarNames_1311_, v___x_1348_);
v___x_1350_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1309_, v_params_1310_, v___x_1349_, v_tail_1323_, v___y_1337_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1373_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1373_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1373_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1372_; 
v_fst_1355_ = lean_ctor_get(v_a_1351_, 0);
v_snd_1356_ = lean_ctor_get(v_a_1351_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1351_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1358_ = v_a_1351_;
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_inc(v_fst_1355_);
lean_dec(v_a_1351_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1372_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_snd_1343_);
lean_ctor_set(v___x_1358_, 0, v_head_1322_);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_head_1322_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_snd_1343_);
v___x_1361_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_snd_1356_);
lean_ctor_set(v___x_1325_, 0, v___x_1361_);
v___x_1363_ = v___x_1325_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_snd_1356_);
v___x_1363_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1363_);
lean_ctor_set(v___x_1345_, 0, v_fst_1355_);
v___x_1365_ = v___x_1345_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_fst_1355_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1365_);
v___x_1367_ = v___x_1353_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1345_);
lean_dec(v_snd_1343_);
lean_del_object(v___x_1325_);
lean_dec(v_head_1322_);
return v___x_1350_;
}
}
}
v___jp_1375_:
{
lean_object* v_ref_1380_; 
v_ref_1380_ = lean_ctor_get(v___y_1376_, 0);
lean_inc(v_ref_1380_);
lean_dec_ref(v___y_1376_);
v___y_1337_ = v_snd_1379_;
v___y_1338_ = v_snd_1378_;
v___y_1339_ = v_fst_1377_;
v___y_1340_ = v_ref_1380_;
goto v___jp_1336_;
}
v___jp_1381_:
{
lean_object* v___x_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; uint8_t v___x_1387_; 
lean_inc_ref(v___y_1382_);
v___x_1384_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1382_);
v_fst_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_fst_1385_);
v_snd_1386_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_snd_1386_);
lean_dec_ref(v___x_1384_);
v___x_1387_ = lean_unbox(v_fst_1385_);
lean_dec(v_fst_1385_);
v___y_1376_ = v___y_1382_;
v_fst_1377_ = v___x_1387_;
v_snd_1378_ = v_snd_1386_;
v_snd_1379_ = v___y_1383_;
goto v___jp_1375_;
}
v___jp_1388_:
{
if (lean_obj_tag(v_tail_1323_) == 0)
{
if (lean_obj_tag(v___y_1391_) == 1)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v___y_1391_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1403_ = lean_ctor_get(v___y_1391_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v___y_1391_, 0);
lean_dec(v_unused_1404_);
v___x_1393_ = v___y_1391_;
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___y_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1402_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = 0;
lean_inc(v_ref_1309_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 6);
lean_ctor_set(v___x_1334_, 1, v_x_1313_);
lean_ctor_set(v___x_1334_, 0, v_ref_1309_);
v___x_1397_ = v___x_1334_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_ref_1309_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_x_1313_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
lean_inc(v___y_1390_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___y_1390_);
lean_ctor_set(v___x_1393_, 0, v___x_1397_);
v___x_1399_ = v___x_1393_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___y_1390_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v___y_1376_ = v___y_1389_;
v_fst_1377_ = v___x_1395_;
v_snd_1378_ = v___x_1399_;
v_snd_1379_ = v___y_1390_;
goto v___jp_1375_;
}
}
}
}
else
{
lean_dec(v___y_1390_);
lean_del_object(v___x_1334_);
lean_dec(v_x_1313_);
v___y_1382_ = v___y_1389_;
v___y_1383_ = v___y_1391_;
goto v___jp_1381_;
}
}
else
{
lean_dec(v___y_1390_);
lean_del_object(v___x_1334_);
lean_dec(v_x_1313_);
v___y_1382_ = v___y_1389_;
v___y_1383_ = v___y_1391_;
goto v___jp_1381_;
}
}
v___jp_1405_:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_box(0);
if (lean_obj_tag(v_x_1313_) == 0)
{
v___y_1389_ = v___y_1406_;
v___y_1390_ = v___x_1407_;
v___y_1391_ = v___x_1407_;
goto v___jp_1388_;
}
else
{
lean_object* v_tail_1408_; 
v_tail_1408_ = lean_ctor_get(v_x_1313_, 1);
lean_inc(v_tail_1408_);
v___y_1389_ = v___y_1406_;
v___y_1390_ = v___x_1407_;
v___y_1391_ = v_tail_1408_;
goto v___jp_1388_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_del_object(v___x_1325_);
lean_dec(v_tail_1323_);
lean_dec(v_head_1322_);
lean_dec(v_x_1313_);
lean_dec_ref(v_altVarNames_1311_);
lean_dec(v_ref_1309_);
v_a_1413_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1330_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1330_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_del_object(v___x_1325_);
lean_dec(v_tail_1323_);
lean_dec(v_head_1322_);
lean_dec(v_x_1313_);
lean_dec_ref(v_altVarNames_1311_);
lean_dec(v_ref_1309_);
v_a_1421_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1327_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1327_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object* v_ref_1430_, lean_object* v_params_1431_, lean_object* v_altVarNames_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1430_, v_params_1431_, v_altVarNames_1432_, v_x_1433_, v_x_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_params_1431_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1441_, lean_object* v_constName_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_constName_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(v_00_u03b1_1449_, v_constName_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1457_, lean_object* v_ref_1458_, lean_object* v_constName_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1458_, v_constName_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_ref_1467_, lean_object* v_constName_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1466_, v_ref_1467_, v_constName_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v_ref_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1475_, lean_object* v_ref_1476_, lean_object* v_msg_1477_, lean_object* v_declHint_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1476_, v_msg_1477_, v_declHint_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_ref_1486_, lean_object* v_msg_1487_, lean_object* v_declHint_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1485_, v_ref_1486_, v_msg_1487_, v_declHint_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v_ref_1486_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_1495_, lean_object* v_declHint_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1495_, v_declHint_1496_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1503_, lean_object* v_declHint_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(v_msg_1503_, v_declHint_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1511_, lean_object* v_ref_1512_, lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1512_, v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_ref_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1520_, v_ref_1521_, v_msg_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v_ref_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1529_, lean_object* v_msg_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_msg_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1537_, v_msg_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object* v_e_1545_, lean_object* v_cont_1546_, lean_object* v_g_1547_, lean_object* v_fs_1548_, lean_object* v_clears_1549_, lean_object* v_a_1550_, lean_object* v_ref_1551_, lean_object* v_a_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Lean_Expr_isFVar(v_e_1545_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_dec(v_ref_1551_);
lean_dec_ref(v_e_1545_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1561_ = lean_apply_11(v_cont_1546_, v_g_1547_, v_fs_1548_, v_clears_1549_, v_a_1550_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, lean_box(0));
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_1551_, v_e_1545_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1562_, 1);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1563_ = lean_apply_11(v_cont_1546_, v_g_1547_, v_fs_1548_, v_clears_1549_, v_a_1550_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, lean_box(0));
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1550_);
lean_dec_ref(v_clears_1549_);
lean_dec(v_fs_1548_);
lean_dec(v_g_1547_);
lean_dec_ref(v_cont_1546_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1562_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object* v_e_1572_, lean_object* v_cont_1573_, lean_object* v_g_1574_, lean_object* v_fs_1575_, lean_object* v_clears_1576_, lean_object* v_a_1577_, lean_object* v_ref_1578_, lean_object* v_a_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(v_e_1572_, v_cont_1573_, v_g_1574_, v_fs_1575_, v_clears_1576_, v_a_1577_, v_ref_1578_, v_a_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v_a_1579_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object* v_x_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
v___x_1596_ = lean_apply_7(v_x_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, lean_box(0));
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object* v_x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(v_x_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object* v_mvarId_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___f_1615_; lean_object* v___x_1616_; 
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1608_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1615_, 0, v_x_1607_);
lean_closure_set(v___f_1615_, 1, v___y_1608_);
lean_closure_set(v___f_1615_, 2, v___y_1609_);
v___x_1616_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1606_, v___f_1615_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
return v___x_1616_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object* v_mvarId_1625_, lean_object* v_x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_1625_, v_x_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object* v_x_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (lean_obj_tag(v_x_1641_) == 1)
{
lean_object* v_fvarId_1647_; lean_object* v___x_1648_; 
v_fvarId_1647_ = lean_ctor_get(v_x_1641_, 0);
lean_inc(v_fvarId_1647_);
lean_dec_ref_known(v_x_1641_, 1);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_fvarId_1647_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1650_ = l_Lean_MessageData_ofExpr(v_x_1641_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v___x_1653_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object* v_x_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(v_x_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1661_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_1666_ = l_Lean_MessageData_ofFormat(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
return v_x_1667_;
}
else
{
lean_object* v_head_1669_; lean_object* v_tail_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1692_; 
v_head_1669_ = lean_ctor_get(v_x_1668_, 0);
v_tail_1670_ = lean_ctor_get(v_x_1668_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1668_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1672_ = v_x_1668_;
v_isShared_1673_ = v_isSharedCheck_1692_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_tail_1670_);
lean_inc(v_head_1669_);
lean_dec(v_x_1668_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1692_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_before_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1690_; 
v_before_1674_ = lean_ctor_get(v_head_1669_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_head_1669_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_head_1669_, 1);
lean_dec(v_unused_1691_);
v___x_1676_ = v_head_1669_;
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_before_1674_);
lean_dec(v_head_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1690_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 7);
lean_ctor_set(v___x_1676_, 1, v___x_1678_);
lean_ctor_set(v___x_1676_, 0, v_x_1667_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_x_1667_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 7);
lean_ctor_set(v___x_1672_, 1, v___x_1681_);
lean_ctor_set(v___x_1672_, 0, v___x_1680_);
v___x_1683_ = v___x_1672_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_MessageData_ofSyntax(v_before_1674_);
v___x_1685_ = l_Lean_indentD(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1683_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v_x_1667_ = v___x_1686_;
v_x_1668_ = v_tail_1670_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_1693_, lean_object* v_opt_1694_){
_start:
{
lean_object* v_name_1695_; lean_object* v_defValue_1696_; lean_object* v_map_1697_; lean_object* v___x_1698_; 
v_name_1695_ = lean_ctor_get(v_opt_1694_, 0);
v_defValue_1696_ = lean_ctor_get(v_opt_1694_, 1);
v_map_1697_ = lean_ctor_get(v_opts_1693_, 0);
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1697_, v_name_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_unbox(v_defValue_1696_);
return v___x_1699_;
}
else
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v___x_1698_, 1);
if (lean_obj_tag(v_val_1700_) == 1)
{
uint8_t v_v_1701_; 
v_v_1701_ = lean_ctor_get_uint8(v_val_1700_, 0);
lean_dec_ref_known(v_val_1700_, 0);
return v_v_1701_;
}
else
{
uint8_t v___x_1702_; 
lean_dec(v_val_1700_);
v___x_1702_ = lean_unbox(v_defValue_1696_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_1703_, lean_object* v_opt_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_1703_, v_opt_1704_);
lean_dec_ref(v_opt_1704_);
lean_dec_ref(v_opts_1703_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_1711_ = l_Lean_MessageData_ofFormat(v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_1712_, lean_object* v_macroStack_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1714_);
v___x_1717_ = l_Lean_Elab_pp_macroStack;
v___x_1718_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v___x_1716_, v___x_1717_);
lean_dec_ref(v___x_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec(v_macroStack_1713_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_msgData_1712_);
return v___x_1719_;
}
else
{
if (lean_obj_tag(v_macroStack_1713_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_msgData_1712_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_after_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1737_; 
v_head_1721_ = lean_ctor_get(v_macroStack_1713_, 0);
lean_inc(v_head_1721_);
v_after_1722_ = lean_ctor_get(v_head_1721_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_head_1721_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v_head_1721_, 0);
lean_dec(v_unused_1738_);
v___x_1724_ = v_head_1721_;
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_after_1722_);
lean_dec(v_head_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 7);
lean_ctor_set(v___x_1724_, 1, v___x_1726_);
lean_ctor_set(v___x_1724_, 0, v_msgData_1712_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_msgData_1712_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_msgData_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1729_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_MessageData_ofSyntax(v_after_1722_);
v___x_1732_ = l_Lean_indentD(v___x_1731_);
v_msgData_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1733_, 0, v___x_1730_);
lean_ctor_set(v_msgData_1733_, 1, v___x_1732_);
v___x_1734_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_1733_, v_macroStack_1713_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_1739_, lean_object* v_macroStack_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_1739_, v_macroStack_1740_, v___y_1741_);
lean_dec_ref(v___y_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_ref_1752_; lean_object* v_macroStack_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_ref_1752_ = lean_ctor_get(v___y_1749_, 2);
v_macroStack_1753_ = lean_ctor_get(v___y_1745_, 1);
v___x_1754_ = l_Lean_Elab_getBetterRef(v_ref_1752_, v_macroStack_1753_);
v___x_1755_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1744_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
lean_inc(v_macroStack_1753_);
v___x_1757_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_1756_, v_macroStack_1753_, v___y_1749_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1754_);
lean_ctor_set(v___x_1762_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(lean_object* v_e_1782_, lean_object* v_a_1783_, lean_object* v_00_u03b1_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1793_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1794_ = l_Lean_MessageData_ofExpr(v_e_1782_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_MessageData_ofExpr(v_a_1783_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_1801_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v_e_1803_, lean_object* v_a_1804_, lean_object* v_00_u03b1_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_1803_, v_a_1804_, v_00_u03b1_1805_, v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
if (lean_obj_tag(v_x_1815_) == 0)
{
if (lean_obj_tag(v_x_1816_) == 0)
{
uint8_t v___x_1817_; 
v___x_1817_ = 1;
return v___x_1817_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = 0;
return v___x_1818_;
}
}
else
{
if (lean_obj_tag(v_x_1816_) == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = 0;
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v_val_1821_; uint8_t v___x_1822_; 
v_val_1820_ = lean_ctor_get(v_x_1815_, 0);
v_val_1821_ = lean_ctor_get(v_x_1816_, 0);
v___x_1822_ = lean_name_eq(v_val_1820_, v_val_1821_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_1823_, v_x_1824_);
lean_dec(v_x_1824_);
lean_dec(v_x_1823_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v_ks_1831_; lean_object* v_vs_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1856_; 
v_ks_1831_ = lean_ctor_get(v_x_1827_, 0);
v_vs_1832_ = lean_ctor_get(v_x_1827_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1834_ = v_x_1827_;
v_isShared_1835_ = v_isSharedCheck_1856_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_vs_1832_);
lean_inc(v_ks_1831_);
lean_dec(v_x_1827_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1856_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = lean_array_get_size(v_ks_1831_);
v___x_1837_ = lean_nat_dec_lt(v_x_1828_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v_x_1828_);
v___x_1838_ = lean_array_push(v_ks_1831_, v_x_1829_);
v___x_1839_ = lean_array_push(v_vs_1832_, v_x_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1839_);
lean_ctor_set(v___x_1834_, 0, v___x_1838_);
v___x_1841_ = v___x_1834_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
else
{
lean_object* v_k_x27_1843_; uint8_t v___x_1844_; 
v_k_x27_1843_ = lean_array_fget_borrowed(v_ks_1831_, v_x_1828_);
v___x_1844_ = l_Lean_instBEqMVarId_beq(v_x_1829_, v_k_x27_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; 
if (v_isShared_1835_ == 0)
{
v___x_1846_ = v___x_1834_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_ks_1831_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_vs_1832_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_add(v_x_1828_, v___x_1847_);
lean_dec(v_x_1828_);
v_x_1827_ = v___x_1846_;
v_x_1828_ = v___x_1848_;
goto _start;
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = lean_array_fset(v_ks_1831_, v_x_1828_, v_x_1829_);
v___x_1852_ = lean_array_fset(v_vs_1832_, v_x_1828_, v_x_1830_);
lean_dec(v_x_1828_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1852_);
lean_ctor_set(v___x_1834_, 0, v___x_1851_);
v___x_1854_ = v___x_1834_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object* v_n_1857_, lean_object* v_k_1858_, lean_object* v_v_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_n_1857_, v___x_1860_, v_k_1858_, v_v_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object* v_x_1863_, size_t v_x_1864_, size_t v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v_es_1868_; size_t v___x_1869_; size_t v___x_1870_; lean_object* v_j_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_es_1868_ = lean_ctor_get(v_x_1863_, 0);
v___x_1869_ = ((size_t)31ULL);
v___x_1870_ = lean_usize_land(v_x_1864_, v___x_1869_);
v_j_1871_ = lean_usize_to_nat(v___x_1870_);
v___x_1872_ = lean_array_get_size(v_es_1868_);
v___x_1873_ = lean_nat_dec_lt(v_j_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_dec(v_j_1871_);
lean_dec(v_x_1867_);
lean_dec(v_x_1866_);
return v_x_1863_;
}
else
{
lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1912_; 
lean_inc_ref(v_es_1868_);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1863_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_x_1863_, 0);
lean_dec(v_unused_1913_);
v___x_1875_ = v_x_1863_;
v_isShared_1876_ = v_isSharedCheck_1912_;
goto v_resetjp_1874_;
}
else
{
lean_dec(v_x_1863_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1912_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_v_1877_; lean_object* v___x_1878_; lean_object* v_xs_x27_1879_; lean_object* v___y_1881_; 
v_v_1877_ = lean_array_fget(v_es_1868_, v_j_1871_);
v___x_1878_ = lean_box(0);
v_xs_x27_1879_ = lean_array_fset(v_es_1868_, v_j_1871_, v___x_1878_);
switch(lean_obj_tag(v_v_1877_))
{
case 0:
{
lean_object* v_key_1886_; lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1897_; 
v_key_1886_ = lean_ctor_get(v_v_1877_, 0);
v_val_1887_ = lean_ctor_get(v_v_1877_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_v_1877_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1889_ = v_v_1877_;
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_inc(v_key_1886_);
lean_dec(v_v_1877_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Lean_instBEqMVarId_beq(v_x_1866_, v_key_1886_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_del_object(v___x_1889_);
v___x_1892_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1886_, v_val_1887_, v_x_1866_, v_x_1867_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
v___y_1881_ = v___x_1893_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_val_1887_);
lean_dec(v_key_1886_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_x_1867_);
lean_ctor_set(v___x_1889_, 0, v_x_1866_);
v___x_1895_ = v___x_1889_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_x_1866_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_x_1867_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v___y_1881_ = v___x_1895_;
goto v___jp_1880_;
}
}
}
}
case 1:
{
lean_object* v_node_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1910_; 
v_node_1898_ = lean_ctor_get(v_v_1877_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_v_1877_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1900_ = v_v_1877_;
v_isShared_1901_ = v_isSharedCheck_1910_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_node_1898_);
lean_dec(v_v_1877_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1910_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
size_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1902_ = ((size_t)5ULL);
v___x_1903_ = lean_usize_shift_right(v_x_1864_, v___x_1902_);
v___x_1904_ = ((size_t)1ULL);
v___x_1905_ = lean_usize_add(v_x_1865_, v___x_1904_);
v___x_1906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_node_1898_, v___x_1903_, v___x_1905_, v_x_1866_, v_x_1867_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1906_);
v___x_1908_ = v___x_1900_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v___y_1881_ = v___x_1908_;
goto v___jp_1880_;
}
}
}
default: 
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_x_1866_);
lean_ctor_set(v___x_1911_, 1, v_x_1867_);
v___y_1881_ = v___x_1911_;
goto v___jp_1880_;
}
}
v___jp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_array_fset(v_xs_x27_1879_, v_j_1871_, v___y_1881_);
lean_dec(v_j_1871_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1882_);
v___x_1884_ = v___x_1875_;
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
}
}
}
else
{
lean_object* v_ks_1914_; lean_object* v_vs_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1933_; 
v_ks_1914_ = lean_ctor_get(v_x_1863_, 0);
v_vs_1915_ = lean_ctor_get(v_x_1863_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1863_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1917_ = v_x_1863_;
v_isShared_1918_ = v_isSharedCheck_1933_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_vs_1915_);
lean_inc(v_ks_1914_);
lean_dec(v_x_1863_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1933_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_ks_1914_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_vs_1915_);
v___x_1920_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v_newNode_1921_; size_t v___x_1922_; uint8_t v___x_1923_; 
v_newNode_1921_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1920_, v_x_1866_, v_x_1867_);
v___x_1922_ = ((size_t)7ULL);
v___x_1923_ = lean_usize_dec_le(v___x_1922_, v_x_1865_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1921_);
v___x_1925_ = lean_unsigned_to_nat(4u);
v___x_1926_ = lean_nat_dec_lt(v___x_1924_, v___x_1925_);
lean_dec(v___x_1924_);
if (v___x_1926_ == 0)
{
lean_object* v_ks_1927_; lean_object* v_vs_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_ks_1927_ = lean_ctor_get(v_newNode_1921_, 0);
lean_inc_ref(v_ks_1927_);
v_vs_1928_ = lean_ctor_get(v_newNode_1921_, 1);
lean_inc_ref(v_vs_1928_);
lean_dec_ref(v_newNode_1921_);
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1865_, v_ks_1927_, v_vs_1928_, v___x_1929_, v___x_1930_);
lean_dec_ref(v_vs_1928_);
lean_dec_ref(v_ks_1927_);
return v___x_1931_;
}
else
{
return v_newNode_1921_;
}
}
else
{
return v_newNode_1921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1934_, lean_object* v_keys_1935_, lean_object* v_vals_1936_, lean_object* v_i_1937_, lean_object* v_entries_1938_){
_start:
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = lean_array_get_size(v_keys_1935_);
v___x_1940_ = lean_nat_dec_lt(v_i_1937_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_dec(v_i_1937_);
return v_entries_1938_;
}
else
{
lean_object* v_k_1941_; lean_object* v_v_1942_; uint64_t v___x_1943_; size_t v_h_1944_; size_t v___x_1945_; lean_object* v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v_h_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_k_1941_ = lean_array_fget_borrowed(v_keys_1935_, v_i_1937_);
v_v_1942_ = lean_array_fget_borrowed(v_vals_1936_, v_i_1937_);
v___x_1943_ = l_Lean_instHashableMVarId_hash(v_k_1941_);
v_h_1944_ = lean_uint64_to_usize(v___x_1943_);
v___x_1945_ = ((size_t)5ULL);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_sub(v_depth_1934_, v___x_1947_);
v___x_1949_ = lean_usize_mul(v___x_1945_, v___x_1948_);
v_h_1950_ = lean_usize_shift_right(v_h_1944_, v___x_1949_);
v___x_1951_ = lean_nat_add(v_i_1937_, v___x_1946_);
lean_dec(v_i_1937_);
lean_inc(v_v_1942_);
lean_inc(v_k_1941_);
v___x_1952_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1938_, v_h_1950_, v_depth_1934_, v_k_1941_, v_v_1942_);
v_i_1937_ = v___x_1951_;
v_entries_1938_ = v___x_1952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1954_, lean_object* v_keys_1955_, lean_object* v_vals_1956_, lean_object* v_i_1957_, lean_object* v_entries_1958_){
_start:
{
size_t v_depth_boxed_1959_; lean_object* v_res_1960_; 
v_depth_boxed_1959_ = lean_unbox_usize(v_depth_1954_);
lean_dec(v_depth_1954_);
v_res_1960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1959_, v_keys_1955_, v_vals_1956_, v_i_1957_, v_entries_1958_);
lean_dec_ref(v_vals_1956_);
lean_dec_ref(v_keys_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
size_t v_x_18592__boxed_1966_; size_t v_x_18593__boxed_1967_; lean_object* v_res_1968_; 
v_x_18592__boxed_1966_ = lean_unbox_usize(v_x_1962_);
lean_dec(v_x_1962_);
v_x_18593__boxed_1967_ = lean_unbox_usize(v_x_1963_);
lean_dec(v_x_1963_);
v_res_1968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1961_, v_x_18592__boxed_1966_, v_x_18593__boxed_1967_, v_x_1964_, v_x_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
uint64_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
v___x_1972_ = l_Lean_instHashableMVarId_hash(v_x_1970_);
v___x_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1969_, v___x_1973_, v___x_1974_, v_x_1970_, v_x_1971_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1976_, lean_object* v_val_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v_mctx_1981_; lean_object* v_cache_1982_; lean_object* v_zetaDeltaFVarIds_1983_; lean_object* v_postponed_1984_; lean_object* v_diag_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2015_; 
v___x_1980_ = lean_st_ref_take(v___y_1978_);
v_mctx_1981_ = lean_ctor_get(v___x_1980_, 0);
v_cache_1982_ = lean_ctor_get(v___x_1980_, 1);
v_zetaDeltaFVarIds_1983_ = lean_ctor_get(v___x_1980_, 2);
v_postponed_1984_ = lean_ctor_get(v___x_1980_, 3);
v_diag_1985_ = lean_ctor_get(v___x_1980_, 4);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1987_ = v___x_1980_;
v_isShared_1988_ = v_isSharedCheck_2015_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_diag_1985_);
lean_inc(v_postponed_1984_);
lean_inc(v_zetaDeltaFVarIds_1983_);
lean_inc(v_cache_1982_);
lean_inc(v_mctx_1981_);
lean_dec(v___x_1980_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2015_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_depth_1989_; lean_object* v_levelAssignDepth_1990_; lean_object* v_lmvarCounter_1991_; lean_object* v_mvarCounter_1992_; lean_object* v_lDecls_1993_; lean_object* v_decls_1994_; lean_object* v_userNames_1995_; lean_object* v_lAssignment_1996_; lean_object* v_eAssignment_1997_; lean_object* v_dAssignment_1998_; lean_object* v_instanceTypedMVars_1999_; lean_object* v_synthNormMemo_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2014_; 
v_depth_1989_ = lean_ctor_get(v_mctx_1981_, 0);
v_levelAssignDepth_1990_ = lean_ctor_get(v_mctx_1981_, 1);
v_lmvarCounter_1991_ = lean_ctor_get(v_mctx_1981_, 2);
v_mvarCounter_1992_ = lean_ctor_get(v_mctx_1981_, 3);
v_lDecls_1993_ = lean_ctor_get(v_mctx_1981_, 4);
v_decls_1994_ = lean_ctor_get(v_mctx_1981_, 5);
v_userNames_1995_ = lean_ctor_get(v_mctx_1981_, 6);
v_lAssignment_1996_ = lean_ctor_get(v_mctx_1981_, 7);
v_eAssignment_1997_ = lean_ctor_get(v_mctx_1981_, 8);
v_dAssignment_1998_ = lean_ctor_get(v_mctx_1981_, 9);
v_instanceTypedMVars_1999_ = lean_ctor_get(v_mctx_1981_, 10);
v_synthNormMemo_2000_ = lean_ctor_get(v_mctx_1981_, 11);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_mctx_1981_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2002_ = v_mctx_1981_;
v_isShared_2003_ = v_isSharedCheck_2014_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_synthNormMemo_2000_);
lean_inc(v_instanceTypedMVars_1999_);
lean_inc(v_dAssignment_1998_);
lean_inc(v_eAssignment_1997_);
lean_inc(v_lAssignment_1996_);
lean_inc(v_userNames_1995_);
lean_inc(v_decls_1994_);
lean_inc(v_lDecls_1993_);
lean_inc(v_mvarCounter_1992_);
lean_inc(v_lmvarCounter_1991_);
lean_inc(v_levelAssignDepth_1990_);
lean_inc(v_depth_1989_);
lean_dec(v_mctx_1981_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2014_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1997_, v_mvarId_1976_, v_val_1977_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 8, v___x_2005_);
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_depth_1989_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_levelAssignDepth_1990_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_lmvarCounter_1991_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_mvarCounter_1992_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_lDecls_1993_);
lean_ctor_set(v_reuseFailAlloc_2013_, 5, v_decls_1994_);
lean_ctor_set(v_reuseFailAlloc_2013_, 6, v_userNames_1995_);
lean_ctor_set(v_reuseFailAlloc_2013_, 7, v_lAssignment_1996_);
lean_ctor_set(v_reuseFailAlloc_2013_, 8, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 9, v_dAssignment_1998_);
lean_ctor_set(v_reuseFailAlloc_2013_, 10, v_instanceTypedMVars_1999_);
lean_ctor_set(v_reuseFailAlloc_2013_, 11, v_synthNormMemo_2000_);
v___x_2007_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_2007_);
v___x_2009_ = v___x_1987_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_cache_1982_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_zetaDeltaFVarIds_1983_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_postponed_1984_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_diag_1985_);
v___x_2009_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_st_ref_put(v___y_1978_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2004_);
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_2016_, lean_object* v_val_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_2016_, v_val_2017_, v___y_2018_);
lean_dec(v___y_2018_);
return v_res_2020_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_14810__overap_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_14810__overap_2031_ = lean_panic_fn_borrowed(v___x_2030_, v_msg_2022_);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
v___x_2032_ = lean_apply_7(v___x_14810__overap_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_2042_, size_t v_i_2043_, size_t v_stop_2044_, lean_object* v_b_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_eq(v_i_2043_, v_stop_2044_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; 
v___x_2047_ = lean_array_uget_borrowed(v_as_2042_, v_i_2043_);
v_fst_2048_ = lean_ctor_get(v___x_2047_, 0);
v_snd_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_snd_2049_);
v___x_2050_ = l_Lean_mkFVar(v_snd_2049_);
lean_inc(v_fst_2048_);
v___x_2051_ = l_Lean_Meta_FVarSubst_insert(v_b_2045_, v_fst_2048_, v___x_2050_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2043_, v___x_2052_);
v_i_2043_ = v___x_2053_;
v_b_2045_ = v___x_2051_;
goto _start;
}
else
{
return v_b_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_2055_, lean_object* v_i_2056_, lean_object* v_stop_2057_, lean_object* v_b_2058_){
_start:
{
size_t v_i_boxed_2059_; size_t v_stop_boxed_2060_; lean_object* v_res_2061_; 
v_i_boxed_2059_ = lean_unbox_usize(v_i_2056_);
lean_dec(v_i_2056_);
v_stop_boxed_2060_ = lean_unbox_usize(v_stop_2057_);
lean_dec(v_stop_2057_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_2055_, v_i_boxed_2059_, v_stop_boxed_2060_, v_b_2058_);
lean_dec_ref(v_as_2055_);
return v_res_2061_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2062_; lean_object* v_dummy_2063_; 
v___x_2062_ = lean_box(0);
v_dummy_2063_ = l_Lean_Expr_sort___override(v___x_2062_);
return v_dummy_2063_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2068_ = lean_unsigned_to_nat(62u);
v___x_2069_ = lean_unsigned_to_nat(323u);
v___x_2070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2072_ = l_mkPanicMessageWithDecl(v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v_snd_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v___x_2078_, lean_object* v_e_2079_, lean_object* v___x_2080_, lean_object* v_head_2081_, lean_object* v_fst_2082_, lean_object* v_tail_2083_, uint8_t v___x_2084_, lean_object* v_snd_2085_, lean_object* v___x_2086_, lean_object* v_fs_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Meta_getElimInfo(v___x_2073_, v___x_2074_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc(v_snd_2075_);
v___x_2097_ = l_Lean_MVarId_getTag(v_snd_2075_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
lean_inc(v_a_2096_);
v___x_2099_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_2096_, v___x_2076_, v_a_2098_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_elimApp_2101_; lean_object* v_alts_2102_; lean_object* v_motivePos_2103_; lean_object* v_nargs_2104_; lean_object* v_dummy_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v_elimApp_2101_ = lean_ctor_get(v_a_2100_, 0);
lean_inc_ref_n(v_elimApp_2101_, 2);
v_alts_2102_ = lean_ctor_get(v_a_2100_, 3);
lean_inc_ref(v_alts_2102_);
lean_dec(v_a_2100_);
v_motivePos_2103_ = lean_ctor_get(v_a_2096_, 2);
lean_inc(v_motivePos_2103_);
lean_dec(v_a_2096_);
v_nargs_2104_ = l_Lean_Expr_getAppNumArgs(v_elimApp_2101_);
v_dummy_2105_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0);
lean_inc(v_nargs_2104_);
v___x_2106_ = lean_mk_array(v_nargs_2104_, v_dummy_2105_);
v___x_2107_ = lean_nat_sub(v_nargs_2104_, v___x_2077_);
lean_dec(v_nargs_2104_);
v___x_2108_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_2101_, v___x_2106_, v___x_2107_);
v___x_2109_ = lean_array_get(v___x_2078_, v___x_2108_, v_motivePos_2103_);
lean_dec(v_motivePos_2103_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = l_Lean_Expr_mvarId_x21(v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Lean_Expr_fvarId_x21(v_e_2079_);
v___x_2112_ = lean_mk_empty_array_with_capacity(v___x_2077_);
lean_inc_ref(v___x_2112_);
v___x_2113_ = lean_array_push(v___x_2112_, v___x_2111_);
v___x_2114_ = lean_mk_empty_array_with_capacity(v___x_2080_);
lean_inc(v_snd_2075_);
v___x_2115_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_2075_, v___x_2110_, v___x_2113_, v___x_2114_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2115_, 1);
v___x_2116_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_2075_, v_elimApp_2101_, v___y_2091_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
lean_dec_ref_known(v___x_2116_, 1);
v___x_2117_ = lean_array_get_size(v_alts_2102_);
v___x_2118_ = lean_nat_dec_eq(v___x_2117_, v___x_2077_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v_alts_2102_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
v___x_2119_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__4);
v___x_2120_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2119_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v_name_2122_; lean_object* v_mvarId_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2191_; 
v___x_2121_ = lean_array_fget(v_alts_2102_, v___x_2080_);
lean_dec_ref(v_alts_2102_);
v_name_2122_ = lean_ctor_get(v___x_2121_, 0);
v_mvarId_2123_ = lean_ctor_get(v___x_2121_, 2);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v___x_2121_, 1);
lean_dec(v_unused_2192_);
v___x_2125_ = v___x_2121_;
v_isShared_2126_ = v_isSharedCheck_2191_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_mvarId_2123_);
lean_inc(v_name_2122_);
lean_dec(v___x_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2191_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_MVarId_intro(v_mvarId_2123_, v_head_2081_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2182_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v_fst_2129_ = lean_ctor_get(v_a_2128_, 0);
v_snd_2130_ = lean_ctor_get(v_a_2128_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2132_ = v_a_2128_;
v_isShared_2133_ = v_isSharedCheck_2182_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_snd_2130_);
lean_inc(v_fst_2129_);
lean_dec(v_a_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2182_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_array_get_size(v_fst_2082_);
v___x_2135_ = l_Lean_Meta_introNCore(v_snd_2130_, v___x_2134_, v_tail_2083_, v___x_2084_, v___x_2118_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2173_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2173_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2173_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2172_; 
v_fst_2140_ = lean_ctor_get(v_a_2136_, 0);
v_snd_2141_ = lean_ctor_get(v_a_2136_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2136_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2143_ = v_a_2136_;
v_isShared_2144_ = v_isSharedCheck_2172_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snd_2141_);
lean_inc(v_fst_2140_);
lean_dec(v_a_2136_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2172_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___y_2146_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2166_ = l_Array_zip___redArg(v_fst_2082_, v_fst_2140_);
lean_dec(v_fst_2140_);
v___x_2167_ = lean_array_get_size(v___x_2166_);
v___x_2168_ = lean_nat_dec_lt(v___x_2080_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v___x_2166_);
v___y_2146_ = v_fs_2087_;
goto v___jp_2145_;
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_of_nat(v___x_2167_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2166_, v___x_2169_, v___x_2170_, v_fs_2087_);
lean_dec_ref(v___x_2166_);
v___y_2146_ = v___x_2171_;
goto v___jp_2145_;
}
v___jp_2145_:
{
lean_object* v___x_2148_; 
lean_inc(v_name_2122_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 1, v_snd_2085_);
lean_ctor_set(v___x_2143_, 0, v_name_2122_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_name_2122_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_snd_2085_);
v___x_2148_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_mkFVar(v_fst_2129_);
v___x_2152_ = lean_array_push(v___x_2086_, v___x_2151_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___y_2146_);
lean_ctor_set(v___x_2125_, 1, v___x_2152_);
lean_ctor_set(v___x_2125_, 0, v_snd_2141_);
v___x_2154_ = v___x_2125_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_snd_2141_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v___y_2146_);
v___x_2154_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_name_2122_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_array_push(v___x_2112_, v___x_2156_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v___x_2157_);
lean_ctor_set(v___x_2132_, 0, v___x_2150_);
v___x_2159_ = v___x_2132_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2159_);
v___x_2161_ = v___x_2138_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
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
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_del_object(v___x_2132_);
lean_dec(v_fst_2129_);
lean_del_object(v___x_2125_);
lean_dec(v_name_2122_);
lean_dec_ref(v___x_2112_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
v_a_2174_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2135_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2135_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2125_);
lean_dec(v_name_2122_);
lean_dec_ref(v___x_2112_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
v_a_2183_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2127_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2127_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v_alts_2102_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
v_a_2193_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2116_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2116_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v_alts_2102_);
lean_dec_ref(v_elimApp_2101_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
lean_dec(v_snd_2075_);
v_a_2201_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2115_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2115_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2096_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
lean_dec(v_snd_2075_);
v_a_2209_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2099_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2099_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2096_);
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
lean_dec_ref(v___x_2076_);
lean_dec(v_snd_2075_);
v_a_2217_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2097_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2097_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_fs_2087_);
lean_dec_ref(v___x_2086_);
lean_dec(v_snd_2085_);
lean_dec(v_tail_2083_);
lean_dec(v_head_2081_);
lean_dec_ref(v___x_2076_);
lean_dec(v_snd_2075_);
v_a_2225_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2095_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2095_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2233_ = _args[0];
lean_object* v___x_2234_ = _args[1];
lean_object* v_snd_2235_ = _args[2];
lean_object* v___x_2236_ = _args[3];
lean_object* v___x_2237_ = _args[4];
lean_object* v___x_2238_ = _args[5];
lean_object* v_e_2239_ = _args[6];
lean_object* v___x_2240_ = _args[7];
lean_object* v_head_2241_ = _args[8];
lean_object* v_fst_2242_ = _args[9];
lean_object* v_tail_2243_ = _args[10];
lean_object* v___x_2244_ = _args[11];
lean_object* v_snd_2245_ = _args[12];
lean_object* v___x_2246_ = _args[13];
lean_object* v_fs_2247_ = _args[14];
lean_object* v___y_2248_ = _args[15];
lean_object* v___y_2249_ = _args[16];
lean_object* v___y_2250_ = _args[17];
lean_object* v___y_2251_ = _args[18];
lean_object* v___y_2252_ = _args[19];
lean_object* v___y_2253_ = _args[20];
lean_object* v___y_2254_ = _args[21];
_start:
{
uint8_t v___x_18877__boxed_2255_; lean_object* v_res_2256_; 
v___x_18877__boxed_2255_ = lean_unbox(v___x_2244_);
v_res_2256_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v___x_2233_, v___x_2234_, v_snd_2235_, v___x_2236_, v___x_2237_, v___x_2238_, v_e_2239_, v___x_2240_, v_head_2241_, v_fst_2242_, v_tail_2243_, v___x_18877__boxed_2255_, v_snd_2245_, v___x_2246_, v_fs_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_fst_2242_);
lean_dec(v___x_2240_);
lean_dec_ref(v_e_2239_);
lean_dec_ref(v___x_2238_);
lean_dec(v___x_2237_);
return v_res_2256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3));
v___x_2258_ = lean_unsigned_to_nat(76u);
v___x_2259_ = lean_unsigned_to_nat(315u);
v___x_2260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1));
v___x_2262_ = l_mkPanicMessageWithDecl(v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_, v___x_2257_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(uint8_t v___x_2270_, lean_object* v_e_2271_, lean_object* v___x_2272_, lean_object* v_g_2273_, lean_object* v___x_2274_, lean_object* v_fs_2275_, lean_object* v_pat_2276_, lean_object* v_____r_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2333_; lean_object* v___x_2339_; 
v___x_2339_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2276_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2333_ = v___x_2340_;
goto v___jp_2332_;
}
else
{
lean_object* v_head_2341_; 
v_head_2341_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_head_2341_);
lean_dec_ref_known(v___x_2339_, 2);
v___y_2333_ = v_head_2341_;
goto v___jp_2332_;
}
v___jp_2285_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
v___x_2287_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2286_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2287_;
}
v___jp_2288_:
{
uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_fst_2300_; 
v___x_2292_ = 0;
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2295_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2292_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 1, v___x_2270_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 2, v___x_2270_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 3, v___x_2270_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 4, v___x_2270_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 5, v___x_2270_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1 + 6, v___x_2270_);
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
lean_inc_ref(v___x_2297_);
v___x_2298_ = lean_array_push(v___x_2297_, v___x_2295_);
v___x_2299_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2291_, v___x_2298_, v___y_2290_, v___x_2293_, v___y_2289_);
lean_dec_ref(v___x_2298_);
v_fst_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_fst_2300_);
if (lean_obj_tag(v_fst_2300_) == 1)
{
lean_object* v_tail_2301_; 
v_tail_2301_ = lean_ctor_get(v_fst_2300_, 1);
lean_inc(v_tail_2301_);
if (lean_obj_tag(v_tail_2301_) == 0)
{
lean_object* v_snd_2302_; lean_object* v_head_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_snd_2302_ = lean_ctor_get(v___x_2299_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v___x_2299_);
v_head_2303_ = lean_ctor_get(v_fst_2300_, 0);
lean_inc(v_head_2303_);
lean_dec_ref_known(v_fst_2300_, 2);
lean_inc_ref(v_e_2271_);
lean_inc_ref(v___x_2297_);
v___x_2304_ = lean_array_push(v___x_2297_, v_e_2271_);
v___x_2305_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2304_, v___x_2272_, v___x_2270_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = l_Lean_MVarId_revert(v_g_2273_, v_a_2306_, v___x_2270_, v___x_2270_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v_fst_2309_; lean_object* v_snd_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v_fst_2309_ = lean_ctor_get(v_a_2308_, 0);
lean_inc(v_fst_2309_);
v_snd_2310_ = lean_ctor_get(v_a_2308_, 1);
lean_inc_n(v_snd_2310_, 2);
lean_dec(v_a_2308_);
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4));
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_box(v___x_2270_);
v___f_2314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed), 22, 15);
lean_closure_set(v___f_2314_, 0, v___x_2311_);
lean_closure_set(v___f_2314_, 1, v___x_2312_);
lean_closure_set(v___f_2314_, 2, v_snd_2310_);
lean_closure_set(v___f_2314_, 3, v___x_2304_);
lean_closure_set(v___f_2314_, 4, v___x_2296_);
lean_closure_set(v___f_2314_, 5, v___x_2274_);
lean_closure_set(v___f_2314_, 6, v_e_2271_);
lean_closure_set(v___f_2314_, 7, v___x_2293_);
lean_closure_set(v___f_2314_, 8, v_head_2303_);
lean_closure_set(v___f_2314_, 9, v_fst_2309_);
lean_closure_set(v___f_2314_, 10, v_tail_2301_);
lean_closure_set(v___f_2314_, 11, v___x_2313_);
lean_closure_set(v___f_2314_, 12, v_snd_2302_);
lean_closure_set(v___f_2314_, 13, v___x_2297_);
lean_closure_set(v___f_2314_, 14, v_fs_2275_);
v___x_2315_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2310_, v___f_2314_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2315_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v___x_2304_);
lean_dec(v_head_2303_);
lean_dec(v_snd_2302_);
lean_dec_ref(v___x_2297_);
lean_dec(v_fs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v_e_2271_);
v_a_2316_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2307_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2307_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v___x_2304_);
lean_dec(v_head_2303_);
lean_dec(v_snd_2302_);
lean_dec_ref(v___x_2297_);
lean_dec(v_fs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec(v_g_2273_);
lean_dec_ref(v_e_2271_);
v_a_2324_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2305_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2305_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_dec_ref_known(v_fst_2300_, 2);
lean_dec(v_tail_2301_);
lean_dec_ref(v___x_2299_);
lean_dec_ref(v___x_2297_);
lean_dec(v_fs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec(v_g_2273_);
lean_dec(v___x_2272_);
lean_dec_ref(v_e_2271_);
goto v___jp_2285_;
}
}
else
{
lean_dec(v_fst_2300_);
lean_dec_ref(v___x_2299_);
lean_dec_ref(v___x_2297_);
lean_dec(v_fs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec(v_g_2273_);
lean_dec(v___x_2272_);
lean_dec_ref(v_e_2271_);
goto v___jp_2285_;
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v_ref_2337_; uint8_t v___x_2338_; 
lean_inc_ref(v___y_2333_);
v___x_2334_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2333_);
v_fst_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_fst_2335_);
v_snd_2336_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_snd_2336_);
lean_dec_ref(v___x_2334_);
v_ref_2337_ = lean_ctor_get(v___y_2333_, 0);
lean_inc(v_ref_2337_);
lean_dec_ref(v___y_2333_);
v___x_2338_ = lean_unbox(v_fst_2335_);
lean_dec(v_fst_2335_);
v___y_2289_ = v_snd_2336_;
v___y_2290_ = v___x_2338_;
v___y_2291_ = v_ref_2337_;
goto v___jp_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object* v___x_2342_, lean_object* v_e_2343_, lean_object* v___x_2344_, lean_object* v_g_2345_, lean_object* v___x_2346_, lean_object* v_fs_2347_, lean_object* v_pat_2348_, lean_object* v_____r_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_19241__boxed_2357_; lean_object* v_res_2358_; 
v___x_19241__boxed_2357_ = lean_unbox(v___x_2342_);
v_res_2358_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_19241__boxed_2357_, v_e_2343_, v___x_2344_, v_g_2345_, v___x_2346_, v_fs_2347_, v_pat_2348_, v_____r_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2359_, lean_object* v_cont_2360_, lean_object* v_g_2361_, lean_object* v_fs_2362_, lean_object* v_clears_2363_, lean_object* v_a_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2359_, v_cont_2360_, v_g_2361_, v_fs_2362_, v_clears_2363_, v_a_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2374_, lean_object* v_g_2375_, lean_object* v_fs_2376_, lean_object* v_clears_2377_, lean_object* v_a_2378_, lean_object* v_cont_2379_, lean_object* v_ref_2380_, lean_object* v_p_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2389_ = lean_box(0);
lean_inc_ref(v_e_2374_);
v___x_2390_ = l_Lean_Expr_mdata___override(v___x_2389_, v_e_2374_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_box(0);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2380_, v___x_2390_, v___x_2391_, v___x_2391_, v___x_2392_, v___x_2393_, v___x_2393_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v___x_2395_; 
lean_dec_ref_known(v___x_2394_, 1);
v___x_2395_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2375_, v_fs_2376_, v_clears_2377_, v_e_2374_, v_a_2378_, v_p_2381_, v_cont_2379_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec_ref(v_e_2374_);
return v___x_2395_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec_ref(v_p_2381_);
lean_dec_ref(v_cont_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_clears_2377_);
lean_dec(v_fs_2376_);
lean_dec(v_g_2375_);
lean_dec_ref(v_e_2374_);
v_a_2396_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2394_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2404_, lean_object* v_g_2405_, lean_object* v_fs_2406_, lean_object* v_clears_2407_, lean_object* v_a_2408_, lean_object* v_cont_2409_, lean_object* v_ref_2410_, lean_object* v_p_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2404_, v_g_2405_, v_fs_2406_, v_clears_2407_, v_a_2408_, v_cont_2409_, v_ref_2410_, v_p_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2420_, lean_object* v_clears_2421_, lean_object* v_cont_2422_, lean_object* v_a_2423_, lean_object* v_goal_2424_, lean_object* v_ctorName_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
if (lean_obj_tag(v_a_2426_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_goal_2424_);
lean_dec_ref(v_cont_2422_);
lean_dec_ref(v_clears_2421_);
lean_dec(v_fs_2420_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2426_);
lean_ctor_set(v___x_2434_, 1, v_a_2423_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
else
{
lean_object* v_head_2436_; lean_object* v_tail_2437_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2472_; 
v_head_2436_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_head_2436_);
v_tail_2437_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_tail_2437_);
lean_dec_ref_known(v_a_2426_, 2);
v_fst_2438_ = lean_ctor_get(v_head_2436_, 0);
v_snd_2439_ = lean_ctor_get(v_head_2436_, 1);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_head_2436_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2441_ = v_head_2436_;
v_isShared_2442_ = v_isSharedCheck_2472_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_snd_2439_);
lean_inc(v_fst_2438_);
lean_dec(v_head_2436_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2472_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v_fst_2438_);
v___x_2444_ = l_instBEqOption_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2443_, v_ctorName_2425_);
lean_dec_ref_known(v___x_2443_, 1);
if (v___x_2444_ == 0)
{
lean_del_object(v___x_2441_);
lean_dec(v_snd_2439_);
v_a_2426_ = v_tail_2437_;
goto _start;
}
else
{
lean_object* v_mvarId_2446_; lean_object* v_fields_2447_; lean_object* v_subst_2448_; lean_object* v_fs_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_mvarId_2446_ = lean_ctor_get(v_goal_2424_, 0);
lean_inc(v_mvarId_2446_);
v_fields_2447_ = lean_ctor_get(v_goal_2424_, 1);
lean_inc_ref(v_fields_2447_);
v_subst_2448_ = lean_ctor_get(v_goal_2424_, 2);
lean_inc(v_subst_2448_);
lean_dec_ref(v_goal_2424_);
v_fs_2449_ = l_Lean_Meta_FVarSubst_append(v_fs_2420_, v_subst_2448_);
v___x_2450_ = lean_array_to_list(v_fields_2447_);
v___x_2451_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_snd_2439_, v___x_2450_);
v___x_2452_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2446_, v_fs_2449_, v_clears_2421_, v_a_2423_, v___x_2451_, v_cont_2422_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2463_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v_a_2453_);
lean_ctor_set(v___x_2441_, 0, v_tail_2437_);
v___x_2458_ = v___x_2441_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_tail_2437_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2460_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_del_object(v___x_2441_);
lean_dec(v_tail_2437_);
v_a_2464_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2452_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2452_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2473_, lean_object* v_clears_2474_, lean_object* v_cont_2475_, lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
if (v___x_2487_ == 0)
{
lean_object* v_fst_2488_; lean_object* v_snd_2489_; lean_object* v___x_2490_; lean_object* v_toInductionSubgoal_2491_; lean_object* v_ctorName_2492_; lean_object* v___x_2493_; 
v_fst_2488_ = lean_ctor_get(v_b_2479_, 0);
lean_inc(v_fst_2488_);
v_snd_2489_ = lean_ctor_get(v_b_2479_, 1);
lean_inc(v_snd_2489_);
lean_dec_ref(v_b_2479_);
v___x_2490_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
v_toInductionSubgoal_2491_ = lean_ctor_get(v___x_2490_, 0);
v_ctorName_2492_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_toInductionSubgoal_2491_);
lean_inc_ref(v_cont_2475_);
lean_inc_ref(v_clears_2474_);
lean_inc(v_fs_2473_);
v___x_2493_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2473_, v_clears_2474_, v_cont_2475_, v_snd_2489_, v_toInductionSubgoal_2491_, v_ctorName_2492_, v_fst_2488_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; size_t v___x_2495_; size_t v___x_2496_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = ((size_t)1ULL);
v___x_2496_ = lean_usize_add(v_i_2477_, v___x_2495_);
v_i_2477_ = v___x_2496_;
v_b_2479_ = v_a_2494_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2475_);
lean_dec_ref(v_clears_2474_);
lean_dec(v_fs_2473_);
return v___x_2493_;
}
}
else
{
lean_object* v___x_2498_; 
lean_dec_ref(v_cont_2475_);
lean_dec_ref(v_clears_2474_);
lean_dec(v_fs_2473_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_b_2479_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_a_2501_, lean_object* v_fs_2502_, lean_object* v_clears_2503_, lean_object* v_cont_2504_, lean_object* v_e_2505_, lean_object* v___x_2506_, lean_object* v_g_2507_, lean_object* v___x_2508_, lean_object* v_pat_2509_, lean_object* v___y_2510_, lean_object* v_asFVar_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_fst_2521_; lean_object* v_snd_2522_; lean_object* v___y_2549_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2561_ = lean_box(0);
lean_inc_ref(v_e_2505_);
v___x_2562_ = l_Lean_Expr_mdata___override(v___x_2561_, v_e_2505_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_box(0);
v___x_2565_ = 0;
lean_inc(v___y_2510_);
v___x_2566_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2510_, v___x_2562_, v___x_2563_, v___x_2563_, v___x_2564_, v___x_2565_, v___x_2565_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2566_, 1);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc_ref(v_e_2505_);
v___x_2567_ = lean_apply_6(v_asFVar_2511_, v_e_2505_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, lean_box(0));
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref_known(v___x_2567_, 1);
v___x_2568_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2565_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2569_; 
lean_dec_ref_known(v___x_2568_, 1);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc_ref(v_e_2505_);
v___x_2569_ = lean_infer_type(v_e_2505_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_Meta_whnfD(v_a_2570_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = l_Lean_Expr_getAppFn(v_a_2572_);
if (lean_obj_tag(v___x_2573_) == 4)
{
lean_object* v_declName_2574_; lean_object* v___x_2575_; lean_object* v_env_2576_; lean_object* v___x_2577_; 
v_declName_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_declName_2574_);
lean_dec_ref_known(v___x_2573_, 2);
v___x_2575_ = lean_st_ref_get(v___y_2518_);
v_env_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_env_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l_Lean_Environment_find_x3f(v_env_2576_, v_declName_2574_, v___x_2565_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
v___x_2578_ = lean_box(0);
v___x_2579_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2505_, v_a_2572_, lean_box(0), v___x_2578_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v___y_2549_ = v___x_2579_;
goto v___jp_2548_;
}
else
{
lean_object* v_val_2580_; 
v_val_2580_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v___x_2577_, 1);
switch(lean_obj_tag(v_val_2580_))
{
case 4:
{
lean_object* v_val_2581_; uint8_t v_kind_2582_; 
lean_dec(v___y_2510_);
v_val_2581_ = lean_ctor_get(v_val_2580_, 0);
lean_inc_ref(v_val_2581_);
lean_dec_ref_known(v_val_2580_, 1);
v_kind_2582_ = lean_ctor_get_uint8(v_val_2581_, sizeof(void*)*1);
lean_dec_ref(v_val_2581_);
if (v_kind_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec(v_a_2572_);
v___x_2583_ = lean_box(0);
lean_inc(v_fs_2502_);
v___x_2584_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2565_, v_e_2505_, v___x_2506_, v_g_2507_, v___x_2508_, v_fs_2502_, v_pat_2509_, v___x_2583_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v___y_2549_ = v___x_2584_;
goto v___jp_2548_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_box(0);
lean_inc_ref(v_e_2505_);
v___x_2586_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2505_, v_a_2572_, lean_box(0), v___x_2585_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
lean_inc(v_fs_2502_);
v___x_2588_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2565_, v_e_2505_, v___x_2506_, v_g_2507_, v___x_2508_, v_fs_2502_, v_pat_2509_, v_a_2587_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v___y_2549_ = v___x_2588_;
goto v___jp_2548_;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2589_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2586_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2586_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
case 5:
{
lean_object* v_val_2597_; lean_object* v_numParams_2598_; lean_object* v_ctors_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec(v_a_2572_);
lean_dec_ref(v___x_2508_);
lean_dec(v___x_2506_);
v_val_2597_ = lean_ctor_get(v_val_2580_, 0);
lean_inc_ref(v_val_2597_);
lean_dec_ref_known(v_val_2580_, 1);
v_numParams_2598_ = lean_ctor_get(v_val_2597_, 1);
lean_inc(v_numParams_2598_);
v_ctors_2599_ = lean_ctor_get(v_val_2597_, 4);
lean_inc(v_ctors_2599_);
lean_dec_ref(v_val_2597_);
v___x_2600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2601_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2509_);
v___x_2602_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2510_, v_numParams_2598_, v___x_2600_, v_ctors_2599_, v___x_2601_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v_numParams_2598_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_fst_2604_; lean_object* v_snd_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v_fst_2604_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_fst_2604_);
v_snd_2605_ = lean_ctor_get(v_a_2603_, 1);
lean_inc(v_snd_2605_);
lean_dec(v_a_2603_);
v___x_2606_ = l_Lean_Expr_fvarId_x21(v_e_2505_);
lean_dec_ref(v_e_2505_);
v___x_2607_ = 1;
v___x_2608_ = l_Lean_MVarId_cases(v_g_2507_, v___x_2606_, v_fst_2604_, v___x_2607_, v___x_2563_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v_fst_2521_ = v_snd_2605_;
v_snd_2522_ = v_a_2609_;
goto v___jp_2520_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_snd_2605_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2610_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2608_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2608_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_g_2507_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2618_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2602_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2602_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
default: 
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v_val_2580_);
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
v___x_2626_ = lean_box(0);
v___x_2627_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2505_, v_a_2572_, lean_box(0), v___x_2626_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v___y_2549_ = v___x_2627_;
goto v___jp_2548_;
}
}
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec_ref(v___x_2573_);
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
v___x_2628_ = lean_box(0);
v___x_2629_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v_e_2505_, v_a_2572_, lean_box(0), v___x_2628_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v___y_2549_ = v___x_2629_;
goto v___jp_2548_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2630_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2571_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2571_);
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
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2638_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2569_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2569_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2646_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2568_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2568_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2654_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2567_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2567_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_asFVar_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v_pat_2509_);
lean_dec_ref(v___x_2508_);
lean_dec(v_g_2507_);
lean_dec(v___x_2506_);
lean_dec_ref(v_e_2505_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2662_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2566_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2566_);
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
v___jp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_array_get_size(v_snd_2522_);
v___x_2525_ = lean_nat_dec_lt(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
lean_dec_ref(v_snd_2522_);
lean_dec(v_fst_2521_);
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_a_2501_);
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_fst_2521_);
lean_ctor_set(v___x_2527_, 1, v_a_2501_);
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2524_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2502_, v_clears_2503_, v_cont_2504_, v_snd_2522_, v___x_2528_, v___x_2529_, v___x_2527_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec_ref(v_snd_2522_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_snd_2535_; lean_object* v___x_2537_; 
v_snd_2535_ = lean_ctor_get(v_a_2531_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_a_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v_snd_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_snd_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2530_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2530_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
v___jp_2548_:
{
if (lean_obj_tag(v___y_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v_fst_2551_; lean_object* v_snd_2552_; 
v_a_2550_ = lean_ctor_get(v___y_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___y_2549_, 1);
v_fst_2551_ = lean_ctor_get(v_a_2550_, 0);
lean_inc(v_fst_2551_);
v_snd_2552_ = lean_ctor_get(v_a_2550_, 1);
lean_inc(v_snd_2552_);
lean_dec(v_a_2550_);
v_fst_2521_ = v_fst_2551_;
v_snd_2522_ = v_snd_2552_;
goto v___jp_2520_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_cont_2504_);
lean_dec_ref(v_clears_2503_);
lean_dec(v_fs_2502_);
lean_dec(v_a_2501_);
v_a_2553_ = lean_ctor_get(v___y_2549_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___y_2549_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___y_2549_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___y_2549_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_a_2670_ = _args[0];
lean_object* v_fs_2671_ = _args[1];
lean_object* v_clears_2672_ = _args[2];
lean_object* v_cont_2673_ = _args[3];
lean_object* v_e_2674_ = _args[4];
lean_object* v___x_2675_ = _args[5];
lean_object* v_g_2676_ = _args[6];
lean_object* v___x_2677_ = _args[7];
lean_object* v_pat_2678_ = _args[8];
lean_object* v___y_2679_ = _args[9];
lean_object* v_asFVar_2680_ = _args[10];
lean_object* v_x_2681_ = _args[11];
lean_object* v___y_2682_ = _args[12];
lean_object* v___y_2683_ = _args[13];
lean_object* v___y_2684_ = _args[14];
lean_object* v___y_2685_ = _args[15];
lean_object* v___y_2686_ = _args[16];
lean_object* v___y_2687_ = _args[17];
lean_object* v___y_2688_ = _args[18];
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_a_2670_, v_fs_2671_, v_clears_2672_, v_cont_2673_, v_e_2674_, v___x_2675_, v_g_2676_, v___x_2677_, v_pat_2678_, v___y_2679_, v_asFVar_2680_, v_x_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_x_2681_);
return v_res_2689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2694_ = l_Lean_MessageData_ofFormat(v___x_2693_);
return v___x_2694_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2697_, lean_object* v___f_2698_, lean_object* v_e_2699_, lean_object* v_asFVar_2700_, lean_object* v_g_2701_, lean_object* v_fs_2702_, lean_object* v_cont_2703_, lean_object* v_clears_2704_, lean_object* v_a_2705_, lean_object* v___f_2706_, lean_object* v___f_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
switch(lean_obj_tag(v_pat_2697_))
{
case 1:
{
lean_object* v_a_2715_; 
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___f_2706_);
v_a_2715_ = lean_ctor_get(v_pat_2697_, 1);
lean_inc(v_a_2715_);
if (lean_obj_tag(v_a_2715_) == 1)
{
lean_object* v_pre_2716_; 
v_pre_2716_ = lean_ctor_get(v_a_2715_, 0);
if (lean_obj_tag(v_pre_2716_) == 0)
{
lean_object* v_ref_2717_; lean_object* v_str_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_ref_2717_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2717_);
lean_dec_ref_known(v_pat_2697_, 2);
v_str_2718_ = lean_ctor_get(v_a_2715_, 1);
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2720_ = lean_string_dec_eq(v_str_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2721_ = lean_apply_9(v___f_2698_, v_ref_2717_, v_a_2715_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2721_;
}
else
{
uint8_t v___x_2722_; lean_object* v___x_2723_; 
lean_inc(v_pre_2716_);
lean_dec_ref_known(v_a_2715_, 2);
lean_dec_ref(v___f_2698_);
v___x_2722_ = 0;
v___x_2723_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2722_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec_ref_known(v___x_2723_, 1);
v___x_2724_ = lean_box(0);
lean_inc_ref(v_e_2699_);
v___x_2725_ = l_Lean_Expr_mdata___override(v___x_2724_, v_e_2699_);
v___x_2726_ = lean_box(0);
v___x_2727_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2717_, v___x_2725_, v___x_2726_, v___x_2726_, v_pre_2716_, v___x_2722_, v___x_2722_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v___x_2728_; 
lean_dec_ref_known(v___x_2727_, 1);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
v___x_2728_ = lean_apply_6(v_asFVar_2700_, v_e_2699_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = l_Lean_Meta_substEq(v_g_2701_, v_a_2729_, v_fs_2702_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_fst_2732_; lean_object* v_snd_2733_; lean_object* v___x_2734_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_fst_2732_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_fst_2732_);
v_snd_2733_ = lean_ctor_get(v_a_2731_, 1);
lean_inc(v_snd_2733_);
lean_dec(v_a_2731_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2734_ = lean_apply_11(v_cont_2703_, v_snd_2733_, v_fst_2732_, v_clears_2704_, v_a_2705_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
v_a_2735_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2730_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2730_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
v_a_2743_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2728_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2728_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
v_a_2751_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2727_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2727_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_ref_2717_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
v_a_2759_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2723_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2723_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
else
{
lean_object* v_ref_2767_; lean_object* v___x_2768_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
v_ref_2767_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2767_);
lean_dec_ref_known(v_pat_2697_, 2);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2768_ = lean_apply_9(v___f_2698_, v_ref_2767_, v_a_2715_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2768_;
}
}
else
{
lean_object* v_ref_2769_; lean_object* v___x_2770_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
v_ref_2769_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2769_);
lean_dec_ref_known(v_pat_2697_, 2);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2770_ = lean_apply_9(v___f_2698_, v_ref_2769_, v_a_2715_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2770_;
}
}
case 2:
{
lean_object* v_ref_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; 
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___f_2706_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v___f_2698_);
v_ref_2771_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2771_);
lean_dec_ref_known(v_pat_2697_, 1);
v___x_2772_ = lean_box(0);
lean_inc_ref(v_e_2699_);
v___x_2773_ = l_Lean_Expr_mdata___override(v___x_2772_, v_e_2699_);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_box(0);
v___x_2776_ = 0;
v___x_2777_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2771_, v___x_2773_, v___x_2774_, v___x_2774_, v___x_2775_, v___x_2776_, v___x_2776_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_dec_ref_known(v___x_2777_, 1);
if (lean_obj_tag(v_e_2699_) == 1)
{
lean_object* v_fvarId_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_fvarId_2778_ = lean_ctor_get(v_e_2699_, 0);
lean_inc(v_fvarId_2778_);
lean_dec_ref_known(v_e_2699_, 1);
v___x_2779_ = lean_array_push(v_clears_2704_, v_fvarId_2778_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2780_ = lean_apply_11(v_cont_2703_, v_g_2701_, v_fs_2702_, v___x_2779_, v_a_2705_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; 
lean_dec_ref(v_e_2699_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2781_ = lean_apply_11(v_cont_2703_, v_g_2701_, v_fs_2702_, v_clears_2704_, v_a_2705_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2781_;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2782_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2777_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2777_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
case 4:
{
lean_object* v_ref_2790_; lean_object* v_a_2791_; lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___f_2706_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v___f_2698_);
v_ref_2790_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2790_);
v_a_2791_ = lean_ctor_get(v_pat_2697_, 1);
lean_inc_ref(v_a_2791_);
v_a_2792_ = lean_ctor_get(v_pat_2697_, 2);
lean_inc(v_a_2792_);
lean_dec_ref_known(v_pat_2697_, 3);
v___x_2793_ = lean_box(0);
lean_inc_ref(v_e_2699_);
v___x_2794_ = l_Lean_Expr_mdata___override(v___x_2793_, v_e_2699_);
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_box(0);
v___x_2797_ = 0;
v___x_2798_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2790_, v___x_2794_, v___x_2795_, v___x_2795_, v___x_2796_, v___x_2797_, v___x_2797_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref_known(v___x_2798_, 1);
v___x_2799_ = l_Lean_Elab_Term_elabType(v_a_2792_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___x_2821_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc_ref(v_e_2699_);
v___x_2821_ = lean_infer_type(v_e_2699_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc_n(v_a_2822_, 2);
lean_dec_ref_known(v___x_2821_, 1);
lean_inc(v_a_2800_);
v___x_2823_ = l_Lean_Meta_isExprDefEq(v_a_2822_, v_a_2800_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; uint8_t v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = lean_unbox(v_a_2824_);
lean_dec(v_a_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2699_);
lean_inc(v_a_2800_);
v___x_2827_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2826_, v_a_2800_, v_a_2822_, v_e_2699_, v___x_2795_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_dec_ref_known(v___x_2827_, 1);
v___y_2802_ = v___y_2708_;
v___y_2803_ = v___y_2709_;
v___y_2804_ = v___y_2710_;
v___y_2805_ = v___y_2711_;
v___y_2806_ = v___y_2712_;
v___y_2807_ = v___y_2713_;
goto v___jp_2801_;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_dec(v_a_2822_);
v___y_2802_ = v___y_2708_;
v___y_2803_ = v___y_2709_;
v___y_2804_ = v___y_2710_;
v___y_2805_ = v___y_2711_;
v___y_2806_ = v___y_2712_;
v___y_2807_ = v___y_2713_;
goto v___jp_2801_;
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2822_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2836_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2823_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2823_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2844_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2821_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2821_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
v___jp_2801_:
{
if (lean_obj_tag(v_e_2699_) == 1)
{
lean_object* v_fvarId_2808_; lean_object* v___x_2809_; 
v_fvarId_2808_ = lean_ctor_get(v_e_2699_, 0);
lean_inc(v_fvarId_2808_);
v___x_2809_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2701_, v_fvarId_2808_, v_a_2800_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2811_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2810_, v_fs_2702_, v_clears_2704_, v_e_2699_, v_a_2705_, v_a_2791_, v_cont_2703_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec_ref_known(v_e_2699_, 1);
return v___x_2811_;
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref_known(v_e_2699_, 1);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
v_a_2812_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2809_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2809_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v___x_2820_; 
lean_dec(v_a_2800_);
v___x_2820_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2701_, v_fs_2702_, v_clears_2704_, v_e_2699_, v_a_2705_, v_a_2791_, v_cont_2703_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec_ref(v_e_2699_);
return v___x_2820_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2852_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2799_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2799_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_e_2699_);
v_a_2860_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2798_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2798_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
case 0:
{
lean_object* v_ref_2868_; lean_object* v_a_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v___f_2707_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v___f_2698_);
v_ref_2868_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2868_);
v_a_2869_ = lean_ctor_get(v_pat_2697_, 1);
lean_inc_ref(v_a_2869_);
lean_dec_ref_known(v_pat_2697_, 2);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2870_ = lean_apply_9(v___f_2706_, v_ref_2868_, v_a_2869_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2870_;
}
case 6:
{
lean_object* v_a_2871_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v___f_2698_);
v_a_2871_ = lean_ctor_get(v_pat_2697_, 1);
if (lean_obj_tag(v_a_2871_) == 1)
{
lean_object* v_tail_2872_; 
v_tail_2872_ = lean_ctor_get(v_a_2871_, 1);
if (lean_obj_tag(v_tail_2872_) == 0)
{
lean_object* v_ref_2873_; lean_object* v_head_2874_; lean_object* v___x_2875_; 
lean_inc_ref(v_a_2871_);
lean_dec_ref(v___f_2707_);
v_ref_2873_ = lean_ctor_get(v_pat_2697_, 0);
lean_inc(v_ref_2873_);
lean_dec_ref_known(v_pat_2697_, 2);
v_head_2874_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_head_2874_);
lean_dec_ref_known(v_a_2871_, 2);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2875_ = lean_apply_9(v___f_2706_, v_ref_2873_, v_head_2874_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; 
lean_dec_ref(v___f_2706_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2876_ = lean_apply_8(v___f_2707_, v_pat_2697_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2876_;
}
}
else
{
lean_object* v___x_2877_; 
lean_dec_ref(v___f_2706_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2877_ = lean_apply_8(v___f_2707_, v_pat_2697_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2877_;
}
}
default: 
{
lean_object* v___x_2878_; 
lean_dec_ref(v___f_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_clears_2704_);
lean_dec_ref(v_cont_2703_);
lean_dec(v_fs_2702_);
lean_dec(v_g_2701_);
lean_dec_ref(v_asFVar_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v___f_2698_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2878_ = lean_apply_8(v___f_2707_, v_pat_2697_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
return v___x_2878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2879_ = _args[0];
lean_object* v___f_2880_ = _args[1];
lean_object* v_e_2881_ = _args[2];
lean_object* v_asFVar_2882_ = _args[3];
lean_object* v_g_2883_ = _args[4];
lean_object* v_fs_2884_ = _args[5];
lean_object* v_cont_2885_ = _args[6];
lean_object* v_clears_2886_ = _args[7];
lean_object* v_a_2887_ = _args[8];
lean_object* v___f_2888_ = _args[9];
lean_object* v___f_2889_ = _args[10];
lean_object* v___y_2890_ = _args[11];
lean_object* v___y_2891_ = _args[12];
lean_object* v___y_2892_ = _args[13];
lean_object* v___y_2893_ = _args[14];
lean_object* v___y_2894_ = _args[15];
lean_object* v___y_2895_ = _args[16];
lean_object* v___y_2896_ = _args[17];
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2879_, v___f_2880_, v_e_2881_, v_asFVar_2882_, v_g_2883_, v_fs_2884_, v_cont_2885_, v_clears_2886_, v_a_2887_, v___f_2888_, v___f_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2898_, lean_object* v_fs_2899_, lean_object* v_clears_2900_, lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v_pat_2903_, lean_object* v_cont_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_asFVar_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v_e_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___y_2919_; lean_object* v_ref_2932_; 
v_asFVar_2912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2913_ = lean_box(1);
v___x_2914_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2899_, 3);
v_e_2915_ = l_Lean_Meta_FVarSubst_apply(v_fs_2899_, v_e_2901_);
lean_inc_n(v_a_2902_, 2);
lean_inc_ref_n(v_clears_2900_, 2);
lean_inc_n(v_g_2898_, 2);
lean_inc_ref_n(v_cont_2904_, 2);
lean_inc_ref_n(v_e_2915_, 2);
v___f_2916_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2916_, 0, v_e_2915_);
lean_closure_set(v___f_2916_, 1, v_cont_2904_);
lean_closure_set(v___f_2916_, 2, v_g_2898_);
lean_closure_set(v___f_2916_, 3, v_fs_2899_);
lean_closure_set(v___f_2916_, 4, v_clears_2900_);
lean_closure_set(v___f_2916_, 5, v_a_2902_);
v___f_2917_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2917_, 0, v_e_2915_);
lean_closure_set(v___f_2917_, 1, v_g_2898_);
lean_closure_set(v___f_2917_, 2, v_fs_2899_);
lean_closure_set(v___f_2917_, 3, v_clears_2900_);
lean_closure_set(v___f_2917_, 4, v_a_2902_);
lean_closure_set(v___f_2917_, 5, v_cont_2904_);
v_ref_2932_ = lean_ctor_get(v_pat_2903_, 0);
lean_inc(v_ref_2932_);
v___y_2919_ = v_ref_2932_;
goto v___jp_2918_;
v___jp_2918_:
{
lean_object* v_toCold_2920_; lean_object* v_currRecDepth_2921_; lean_object* v_ref_2922_; uint16_t v_optionFlags_2923_; uint8_t v_suppressElabErrors_2924_; uint8_t v_checkDeprecated_2925_; uint8_t v_isRecordingDeps_2926_; lean_object* v___f_2927_; lean_object* v___y_2928_; lean_object* v_ref_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_toCold_2920_ = lean_ctor_get(v_a_2909_, 0);
v_currRecDepth_2921_ = lean_ctor_get(v_a_2909_, 1);
v_ref_2922_ = lean_ctor_get(v_a_2909_, 2);
v_optionFlags_2923_ = lean_ctor_get_uint16(v_a_2909_, sizeof(void*)*3);
v_suppressElabErrors_2924_ = lean_ctor_get_uint8(v_a_2909_, sizeof(void*)*3 + 2);
v_checkDeprecated_2925_ = lean_ctor_get_uint8(v_a_2909_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2926_ = lean_ctor_get_uint8(v_a_2909_, sizeof(void*)*3 + 4);
lean_inc(v___y_2919_);
lean_inc_ref(v_pat_2903_);
lean_inc_n(v_g_2898_, 2);
lean_inc_ref(v_e_2915_);
lean_inc_ref(v_cont_2904_);
lean_inc_ref(v_clears_2900_);
lean_inc(v_fs_2899_);
lean_inc(v_a_2902_);
v___f_2927_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2927_, 0, v_a_2902_);
lean_closure_set(v___f_2927_, 1, v_fs_2899_);
lean_closure_set(v___f_2927_, 2, v_clears_2900_);
lean_closure_set(v___f_2927_, 3, v_cont_2904_);
lean_closure_set(v___f_2927_, 4, v_e_2915_);
lean_closure_set(v___f_2927_, 5, v___x_2913_);
lean_closure_set(v___f_2927_, 6, v_g_2898_);
lean_closure_set(v___f_2927_, 7, v___x_2914_);
lean_closure_set(v___f_2927_, 8, v_pat_2903_);
lean_closure_set(v___f_2927_, 9, v___y_2919_);
lean_closure_set(v___f_2927_, 10, v_asFVar_2912_);
v___y_2928_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2928_, 0, v_pat_2903_);
lean_closure_set(v___y_2928_, 1, v___f_2916_);
lean_closure_set(v___y_2928_, 2, v_e_2915_);
lean_closure_set(v___y_2928_, 3, v_asFVar_2912_);
lean_closure_set(v___y_2928_, 4, v_g_2898_);
lean_closure_set(v___y_2928_, 5, v_fs_2899_);
lean_closure_set(v___y_2928_, 6, v_cont_2904_);
lean_closure_set(v___y_2928_, 7, v_clears_2900_);
lean_closure_set(v___y_2928_, 8, v_a_2902_);
lean_closure_set(v___y_2928_, 9, v___f_2917_);
lean_closure_set(v___y_2928_, 10, v___f_2927_);
v_ref_2929_ = l_Lean_replaceRef(v___y_2919_, v_ref_2922_);
lean_dec(v___y_2919_);
lean_inc(v_currRecDepth_2921_);
lean_inc_ref(v_toCold_2920_);
v___x_2930_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2930_, 0, v_toCold_2920_);
lean_ctor_set(v___x_2930_, 1, v_currRecDepth_2921_);
lean_ctor_set(v___x_2930_, 2, v_ref_2929_);
lean_ctor_set_uint16(v___x_2930_, sizeof(void*)*3, v_optionFlags_2923_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*3 + 2, v_suppressElabErrors_2924_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*3 + 3, v_checkDeprecated_2925_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*3 + 4, v_isRecordingDeps_2926_);
v___x_2931_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2898_, v___y_2928_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v___x_2930_, v_a_2910_);
lean_dec_ref_known(v___x_2930_, 3);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2933_, lean_object* v_fs_2934_, lean_object* v_clears_2935_, lean_object* v_a_2936_, lean_object* v_pats_2937_, lean_object* v_cont_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
if (lean_obj_tag(v_pats_2937_) == 0)
{
lean_object* v___x_2946_; 
lean_inc(v_a_2944_);
lean_inc_ref(v_a_2943_);
lean_inc(v_a_2942_);
lean_inc_ref(v_a_2941_);
lean_inc(v_a_2940_);
lean_inc_ref(v_a_2939_);
v___x_2946_ = lean_apply_11(v_cont_2938_, v_g_2933_, v_fs_2934_, v_clears_2935_, v_a_2936_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, lean_box(0));
return v___x_2946_;
}
else
{
lean_object* v_head_2947_; lean_object* v_tail_2948_; lean_object* v_fst_2949_; lean_object* v_snd_2950_; lean_object* v___f_2951_; lean_object* v___x_2952_; 
v_head_2947_ = lean_ctor_get(v_pats_2937_, 0);
lean_inc(v_head_2947_);
v_tail_2948_ = lean_ctor_get(v_pats_2937_, 1);
lean_inc(v_tail_2948_);
lean_dec_ref_known(v_pats_2937_, 2);
v_fst_2949_ = lean_ctor_get(v_head_2947_, 0);
lean_inc(v_fst_2949_);
v_snd_2950_ = lean_ctor_get(v_head_2947_, 1);
lean_inc(v_snd_2950_);
lean_dec(v_head_2947_);
v___f_2951_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2951_, 0, v_tail_2948_);
lean_closure_set(v___f_2951_, 1, v_cont_2938_);
v___x_2952_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2933_, v_fs_2934_, v_clears_2935_, v_snd_2950_, v_a_2936_, v_fst_2949_, v___f_2951_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
lean_dec(v_snd_2950_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2953_, lean_object* v_cont_2954_, lean_object* v_g_2955_, lean_object* v_fs_2956_, lean_object* v_clears_2957_, lean_object* v_a_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2955_, v_fs_2956_, v_clears_2957_, v_a_2958_, v_tail_2953_, v_cont_2954_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2967_, lean_object* v_fs_2968_, lean_object* v_clears_2969_, lean_object* v_a_2970_, lean_object* v_pats_2971_, lean_object* v_cont_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2967_, v_fs_2968_, v_clears_2969_, v_a_2970_, v_pats_2971_, v_cont_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_2981_, lean_object* v_clears_2982_, lean_object* v_cont_2983_, lean_object* v_as_2984_, lean_object* v_i_2985_, lean_object* v_stop_2986_, lean_object* v_b_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
size_t v_i_boxed_2995_; size_t v_stop_boxed_2996_; lean_object* v_res_2997_; 
v_i_boxed_2995_ = lean_unbox_usize(v_i_2985_);
lean_dec(v_i_2985_);
v_stop_boxed_2996_ = lean_unbox_usize(v_stop_2986_);
lean_dec(v_stop_2986_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2981_, v_clears_2982_, v_cont_2983_, v_as_2984_, v_i_boxed_2995_, v_stop_boxed_2996_, v_b_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_as_2984_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_2998_, lean_object* v_clears_2999_, lean_object* v_cont_3000_, lean_object* v_a_3001_, lean_object* v_goal_3002_, lean_object* v_ctorName_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2998_, v_clears_2999_, v_cont_3000_, v_a_3001_, v_goal_3002_, v_ctorName_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_ctorName_3003_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3013_, lean_object* v_fs_3014_, lean_object* v_clears_3015_, lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_pat_3018_, lean_object* v_cont_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3013_, v_fs_3014_, v_clears_3015_, v_e_3016_, v_a_3017_, v_pat_3018_, v_cont_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec_ref(v_e_3016_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3028_, lean_object* v_g_3029_, lean_object* v_fs_3030_, lean_object* v_clears_3031_, lean_object* v_a_3032_, lean_object* v_pats_3033_, lean_object* v_cont_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3029_, v_fs_3030_, v_clears_3031_, v_a_3032_, v_pats_3033_, v_cont_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3043_, lean_object* v_g_3044_, lean_object* v_fs_3045_, lean_object* v_clears_3046_, lean_object* v_a_3047_, lean_object* v_pats_3048_, lean_object* v_cont_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3043_, v_g_3044_, v_fs_3045_, v_clears_3046_, v_a_3047_, v_pats_3048_, v_cont_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3058_, lean_object* v_fs_3059_, lean_object* v_clears_3060_, lean_object* v_cont_3061_, lean_object* v_a_3062_, lean_object* v_goal_3063_, lean_object* v_ctorName_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3059_, v_clears_3060_, v_cont_3061_, v_a_3062_, v_goal_3063_, v_ctorName_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_fs_3075_, lean_object* v_clears_3076_, lean_object* v_cont_3077_, lean_object* v_a_3078_, lean_object* v_goal_3079_, lean_object* v_ctorName_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3074_, v_fs_3075_, v_clears_3076_, v_cont_3077_, v_a_3078_, v_goal_3079_, v_ctorName_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_ctorName_3080_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3090_, lean_object* v_mvarId_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3091_, v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3101_, lean_object* v_mvarId_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3101_, v_mvarId_3102_, v_x_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3112_, lean_object* v_g_3113_, lean_object* v_fs_3114_, lean_object* v_clears_3115_, lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_pat_3118_, lean_object* v_cont_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3113_, v_fs_3114_, v_clears_3115_, v_e_3116_, v_a_3117_, v_pat_3118_, v_cont_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_g_3129_, lean_object* v_fs_3130_, lean_object* v_clears_3131_, lean_object* v_e_3132_, lean_object* v_a_3133_, lean_object* v_pat_3134_, lean_object* v_cont_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3128_, v_g_3129_, v_fs_3130_, v_clears_3131_, v_e_3132_, v_a_3133_, v_pat_3134_, v_cont_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec_ref(v_e_3132_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3144_, lean_object* v_fs_3145_, lean_object* v_clears_3146_, lean_object* v_cont_3147_, lean_object* v_as_3148_, size_t v_i_3149_, size_t v_stop_3150_, lean_object* v_b_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3145_, v_clears_3146_, v_cont_3147_, v_as_3148_, v_i_3149_, v_stop_3150_, v_b_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3160_, lean_object* v_fs_3161_, lean_object* v_clears_3162_, lean_object* v_cont_3163_, lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_stop_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
size_t v_i_boxed_3175_; size_t v_stop_boxed_3176_; lean_object* v_res_3177_; 
v_i_boxed_3175_ = lean_unbox_usize(v_i_3165_);
lean_dec(v_i_3165_);
v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3166_);
lean_dec(v_stop_3166_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3160_, v_fs_3161_, v_clears_3162_, v_cont_3163_, v_as_3164_, v_i_boxed_3175_, v_stop_boxed_3176_, v_b_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v_as_3164_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3178_, lean_object* v_val_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3178_, v_val_3179_, v___y_3183_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3188_, lean_object* v_val_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3188_, v_val_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3198_, lean_object* v_msg_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_msg_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3208_, v_msg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3219_, v_x_3220_, v_x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3223_, lean_object* v_macroStack_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3223_, v_macroStack_3224_, v___y_3229_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3233_, lean_object* v_macroStack_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3233_, v_macroStack_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3243_, lean_object* v_x_3244_, size_t v_x_3245_, size_t v_x_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3244_, v_x_3245_, v_x_3246_, v_x_3247_, v_x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_){
_start:
{
size_t v_x_20541__boxed_3256_; size_t v_x_20542__boxed_3257_; lean_object* v_res_3258_; 
v_x_20541__boxed_3256_ = lean_unbox_usize(v_x_3252_);
lean_dec(v_x_3252_);
v_x_20542__boxed_3257_ = lean_unbox_usize(v_x_3253_);
lean_dec(v_x_3253_);
v_res_3258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3250_, v_x_3251_, v_x_20541__boxed_3256_, v_x_20542__boxed_3257_, v_x_3254_, v_x_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3259_, lean_object* v_n_3260_, lean_object* v_k_3261_, lean_object* v_v_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3260_, v_k_3261_, v_v_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3264_, size_t v_depth_3265_, lean_object* v_keys_3266_, lean_object* v_vals_3267_, lean_object* v_heq_3268_, lean_object* v_i_3269_, lean_object* v_entries_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3265_, v_keys_3266_, v_vals_3267_, v_i_3269_, v_entries_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3272_, lean_object* v_depth_3273_, lean_object* v_keys_3274_, lean_object* v_vals_3275_, lean_object* v_heq_3276_, lean_object* v_i_3277_, lean_object* v_entries_3278_){
_start:
{
size_t v_depth_boxed_3279_; lean_object* v_res_3280_; 
v_depth_boxed_3279_ = lean_unbox_usize(v_depth_3273_);
lean_dec(v_depth_3273_);
v_res_3280_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3272_, v_depth_boxed_3279_, v_keys_3274_, v_vals_3275_, v_heq_3276_, v_i_3277_, v_entries_3278_);
lean_dec_ref(v_vals_3275_);
lean_dec_ref(v_keys_3274_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3282_, v_x_3283_, v_x_3284_, v_x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3287_, lean_object* v_as_3288_, size_t v_i_3289_, size_t v_stop_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = lean_usize_dec_eq(v_i_3289_, v_stop_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = lean_array_uget_borrowed(v_as_3288_, v_i_3289_);
v___x_3293_ = l_Lean_instBEqFVarId_beq(v_a_3287_, v___x_3292_);
if (v___x_3293_ == 0)
{
size_t v___x_3294_; size_t v___x_3295_; 
v___x_3294_ = ((size_t)1ULL);
v___x_3295_ = lean_usize_add(v_i_3289_, v___x_3294_);
v_i_3289_ = v___x_3295_;
goto _start;
}
else
{
return v___x_3293_;
}
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = 0;
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3298_, lean_object* v_as_3299_, lean_object* v_i_3300_, lean_object* v_stop_3301_){
_start:
{
size_t v_i_boxed_3302_; size_t v_stop_boxed_3303_; uint8_t v_res_3304_; lean_object* v_r_3305_; 
v_i_boxed_3302_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_stop_boxed_3303_ = lean_unbox_usize(v_stop_3301_);
lean_dec(v_stop_3301_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3298_, v_as_3299_, v_i_boxed_3302_, v_stop_boxed_3303_);
lean_dec_ref(v_as_3299_);
lean_dec(v_a_3298_);
v_r_3305_ = lean_box(v_res_3304_);
return v_r_3305_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_array_get_size(v_as_3306_);
v___x_3310_ = lean_nat_dec_lt(v___x_3308_, v___x_3309_);
if (v___x_3310_ == 0)
{
return v___x_3310_;
}
else
{
size_t v___x_3311_; size_t v___x_3312_; uint8_t v___x_3313_; 
v___x_3311_ = ((size_t)0ULL);
v___x_3312_ = lean_usize_of_nat(v___x_3309_);
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3307_, v_as_3306_, v___x_3311_, v___x_3312_);
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3314_, lean_object* v_a_3315_){
_start:
{
uint8_t v_res_3316_; lean_object* v_r_3317_; 
v_res_3316_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_as_3314_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3318_, v___y_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3321_, lean_object* v___y_3322_){
_start:
{
uint8_t v_res_3323_; lean_object* v_r_3324_; 
v_res_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec(v_snd_3321_);
v_r_3324_ = lean_box(v_res_3323_);
return v_r_3324_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = 0;
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3327_){
_start:
{
uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3327_);
lean_dec(v_x_3327_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_box(0);
v___x_3332_ = lean_unsigned_to_nat(16u);
v___x_3333_ = lean_mk_array(v___x_3332_, v___x_3331_);
return v___x_3333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3337_, size_t v_sz_3338_, size_t v_i_3339_, lean_object* v_b_3340_, lean_object* v___y_3341_){
_start:
{
uint8_t v___x_3343_; 
v___x_3343_ = lean_usize_dec_lt(v_i_3339_, v_sz_3338_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_b_3340_);
return v___x_3344_;
}
else
{
lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3477_; 
v_snd_3345_ = lean_ctor_get(v_b_3340_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_b_3340_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_b_3340_, 0);
lean_dec(v_unused_3478_);
v___x_3347_ = v_b_3340_;
v_isShared_3348_ = v_isSharedCheck_3477_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_dec(v_b_3340_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3477_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_a_3351_; lean_object* v_a_3358_; 
v___x_3349_ = lean_box(0);
v_a_3358_ = lean_array_uget_borrowed(v_as_3337_, v_i_3339_);
if (lean_obj_tag(v_a_3358_) == 0)
{
v_a_3351_ = v_snd_3345_;
goto v___jp_3350_;
}
else
{
lean_object* v_val_3359_; uint8_t v_a_3361_; lean_object* v___f_3364_; lean_object* v___f_3365_; 
v_val_3359_ = lean_ctor_get(v_a_3358_, 0);
v___f_3364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3345_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3365_, 0, v_snd_3345_);
if (lean_obj_tag(v_val_3359_) == 0)
{
lean_object* v_type_3366_; lean_object* v___x_3367_; uint8_t v_fst_3369_; lean_object* v_mctx_3370_; lean_object* v___y_3386_; lean_object* v_mctx_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v_type_3366_ = lean_ctor_get(v_val_3359_, 3);
v___x_3367_ = lean_st_ref_get(v___y_3341_);
v_mctx_3391_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref_n(v_mctx_3391_, 2);
lean_dec(v___x_3367_);
v___x_3392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v_mctx_3391_);
v___x_3394_ = l_Lean_Expr_hasFVar(v_type_3366_);
if (v___x_3394_ == 0)
{
uint8_t v___x_3395_; 
v___x_3395_ = l_Lean_Expr_hasMVar(v_type_3366_);
if (v___x_3395_ == 0)
{
lean_dec_ref_known(v___x_3393_, 2);
lean_dec_ref(v___f_3365_);
v_fst_3369_ = v___x_3395_;
v_mctx_3370_ = v_mctx_3391_;
goto v___jp_3368_;
}
else
{
lean_object* v___x_3396_; 
lean_dec_ref(v_mctx_3391_);
lean_inc_ref(v_type_3366_);
v___x_3396_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3366_, v___x_3393_);
v___y_3386_ = v___x_3396_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3397_; 
lean_dec_ref(v_mctx_3391_);
lean_inc_ref(v_type_3366_);
v___x_3397_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3366_, v___x_3393_);
v___y_3386_ = v___x_3397_;
goto v___jp_3385_;
}
v___jp_3368_:
{
lean_object* v___x_3371_; lean_object* v_cache_3372_; lean_object* v_zetaDeltaFVarIds_3373_; lean_object* v_postponed_3374_; lean_object* v_diag_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3383_; 
v___x_3371_ = lean_st_ref_take(v___y_3341_);
v_cache_3372_ = lean_ctor_get(v___x_3371_, 1);
v_zetaDeltaFVarIds_3373_ = lean_ctor_get(v___x_3371_, 2);
v_postponed_3374_ = lean_ctor_get(v___x_3371_, 3);
v_diag_3375_ = lean_ctor_get(v___x_3371_, 4);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v___x_3371_, 0);
lean_dec(v_unused_3384_);
v___x_3377_ = v___x_3371_;
v_isShared_3378_ = v_isSharedCheck_3383_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_diag_3375_);
lean_inc(v_postponed_3374_);
lean_inc(v_zetaDeltaFVarIds_3373_);
lean_inc(v_cache_3372_);
lean_dec(v___x_3371_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3383_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v_mctx_3370_);
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_mctx_3370_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_cache_3372_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_zetaDeltaFVarIds_3373_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_postponed_3374_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_diag_3375_);
v___x_3380_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_st_ref_put(v___y_3341_, v___x_3380_);
v_a_3361_ = v_fst_3369_;
goto v___jp_3360_;
}
}
}
v___jp_3385_:
{
lean_object* v_snd_3387_; lean_object* v_fst_3388_; lean_object* v_mctx_3389_; uint8_t v___x_3390_; 
v_snd_3387_ = lean_ctor_get(v___y_3386_, 1);
lean_inc(v_snd_3387_);
v_fst_3388_ = lean_ctor_get(v___y_3386_, 0);
lean_inc(v_fst_3388_);
lean_dec_ref(v___y_3386_);
v_mctx_3389_ = lean_ctor_get(v_snd_3387_, 1);
lean_inc_ref(v_mctx_3389_);
lean_dec(v_snd_3387_);
v___x_3390_ = lean_unbox(v_fst_3388_);
lean_dec(v_fst_3388_);
v_fst_3369_ = v___x_3390_;
v_mctx_3370_ = v_mctx_3389_;
goto v___jp_3368_;
}
}
else
{
uint8_t v_nondep_3398_; 
v_nondep_3398_ = lean_ctor_get_uint8(v_val_3359_, sizeof(void*)*5);
if (v_nondep_3398_ == 0)
{
lean_object* v_type_3399_; lean_object* v_value_3400_; lean_object* v___x_3401_; uint8_t v_fst_3403_; lean_object* v_snd_3404_; lean_object* v___y_3421_; lean_object* v_snd_3426_; lean_object* v___y_3432_; lean_object* v_mctx_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v_type_3399_ = lean_ctor_get(v_val_3359_, 3);
v_value_3400_ = lean_ctor_get(v_val_3359_, 4);
v___x_3401_ = lean_st_ref_get(v___y_3341_);
v_mctx_3438_ = lean_ctor_get(v___x_3401_, 0);
lean_inc_ref(v_mctx_3438_);
lean_dec(v___x_3401_);
v___x_3439_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v_mctx_3438_);
v___x_3441_ = l_Lean_Expr_hasFVar(v_type_3399_);
if (v___x_3441_ == 0)
{
uint8_t v___x_3442_; 
v___x_3442_ = l_Lean_Expr_hasMVar(v_type_3399_);
if (v___x_3442_ == 0)
{
v_snd_3426_ = v___x_3440_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3443_; 
lean_inc_ref(v_type_3399_);
lean_inc_ref(v___f_3365_);
v___x_3443_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3399_, v___x_3440_);
v___y_3432_ = v___x_3443_;
goto v___jp_3431_;
}
}
else
{
lean_object* v___x_3444_; 
lean_inc_ref(v_type_3399_);
lean_inc_ref(v___f_3365_);
v___x_3444_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3399_, v___x_3440_);
v___y_3432_ = v___x_3444_;
goto v___jp_3431_;
}
v___jp_3402_:
{
lean_object* v_mctx_3405_; lean_object* v___x_3406_; lean_object* v_cache_3407_; lean_object* v_zetaDeltaFVarIds_3408_; lean_object* v_postponed_3409_; lean_object* v_diag_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3418_; 
v_mctx_3405_ = lean_ctor_get(v_snd_3404_, 1);
lean_inc_ref(v_mctx_3405_);
lean_dec_ref(v_snd_3404_);
v___x_3406_ = lean_st_ref_take(v___y_3341_);
v_cache_3407_ = lean_ctor_get(v___x_3406_, 1);
v_zetaDeltaFVarIds_3408_ = lean_ctor_get(v___x_3406_, 2);
v_postponed_3409_ = lean_ctor_get(v___x_3406_, 3);
v_diag_3410_ = lean_ctor_get(v___x_3406_, 4);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v___x_3406_, 0);
lean_dec(v_unused_3419_);
v___x_3412_ = v___x_3406_;
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_diag_3410_);
lean_inc(v_postponed_3409_);
lean_inc(v_zetaDeltaFVarIds_3408_);
lean_inc(v_cache_3407_);
lean_dec(v___x_3406_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v_mctx_3405_);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_mctx_3405_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_cache_3407_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_zetaDeltaFVarIds_3408_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_postponed_3409_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_diag_3410_);
v___x_3415_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_st_ref_put(v___y_3341_, v___x_3415_);
v_a_3361_ = v_fst_3403_;
goto v___jp_3360_;
}
}
}
v___jp_3420_:
{
lean_object* v_fst_3422_; lean_object* v_snd_3423_; uint8_t v___x_3424_; 
v_fst_3422_ = lean_ctor_get(v___y_3421_, 0);
lean_inc(v_fst_3422_);
v_snd_3423_ = lean_ctor_get(v___y_3421_, 1);
lean_inc(v_snd_3423_);
lean_dec_ref(v___y_3421_);
v___x_3424_ = lean_unbox(v_fst_3422_);
lean_dec(v_fst_3422_);
v_fst_3403_ = v___x_3424_;
v_snd_3404_ = v_snd_3423_;
goto v___jp_3402_;
}
v___jp_3425_:
{
uint8_t v___x_3427_; 
v___x_3427_ = l_Lean_Expr_hasFVar(v_value_3400_);
if (v___x_3427_ == 0)
{
uint8_t v___x_3428_; 
v___x_3428_ = l_Lean_Expr_hasMVar(v_value_3400_);
if (v___x_3428_ == 0)
{
lean_dec_ref(v___f_3365_);
v_fst_3403_ = v___x_3428_;
v_snd_3404_ = v_snd_3426_;
goto v___jp_3402_;
}
else
{
lean_object* v___x_3429_; 
lean_inc_ref(v_value_3400_);
v___x_3429_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_value_3400_, v_snd_3426_);
v___y_3421_ = v___x_3429_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3430_; 
lean_inc_ref(v_value_3400_);
v___x_3430_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_value_3400_, v_snd_3426_);
v___y_3421_ = v___x_3430_;
goto v___jp_3420_;
}
}
v___jp_3431_:
{
lean_object* v_fst_3433_; uint8_t v___x_3434_; 
v_fst_3433_ = lean_ctor_get(v___y_3432_, 0);
v___x_3434_ = lean_unbox(v_fst_3433_);
if (v___x_3434_ == 0)
{
lean_object* v_snd_3435_; 
v_snd_3435_ = lean_ctor_get(v___y_3432_, 1);
lean_inc(v_snd_3435_);
lean_dec_ref(v___y_3432_);
v_snd_3426_ = v_snd_3435_;
goto v___jp_3425_;
}
else
{
lean_object* v_snd_3436_; uint8_t v___x_3437_; 
lean_inc(v_fst_3433_);
lean_dec_ref(v___f_3365_);
v_snd_3436_ = lean_ctor_get(v___y_3432_, 1);
lean_inc(v_snd_3436_);
lean_dec_ref(v___y_3432_);
v___x_3437_ = lean_unbox(v_fst_3433_);
lean_dec(v_fst_3433_);
v_fst_3403_ = v___x_3437_;
v_snd_3404_ = v_snd_3436_;
goto v___jp_3402_;
}
}
}
else
{
lean_object* v_type_3445_; lean_object* v___x_3446_; uint8_t v_fst_3448_; lean_object* v_mctx_3449_; lean_object* v___y_3465_; lean_object* v_mctx_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v_type_3445_ = lean_ctor_get(v_val_3359_, 3);
v___x_3446_ = lean_st_ref_get(v___y_3341_);
v_mctx_3470_ = lean_ctor_get(v___x_3446_, 0);
lean_inc_ref_n(v_mctx_3470_, 2);
lean_dec(v___x_3446_);
v___x_3471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_mctx_3470_);
v___x_3473_ = l_Lean_Expr_hasFVar(v_type_3445_);
if (v___x_3473_ == 0)
{
uint8_t v___x_3474_; 
v___x_3474_ = l_Lean_Expr_hasMVar(v_type_3445_);
if (v___x_3474_ == 0)
{
lean_dec_ref_known(v___x_3472_, 2);
lean_dec_ref(v___f_3365_);
v_fst_3448_ = v___x_3474_;
v_mctx_3449_ = v_mctx_3470_;
goto v___jp_3447_;
}
else
{
lean_object* v___x_3475_; 
lean_dec_ref(v_mctx_3470_);
lean_inc_ref(v_type_3445_);
v___x_3475_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3445_, v___x_3472_);
v___y_3465_ = v___x_3475_;
goto v___jp_3464_;
}
}
else
{
lean_object* v___x_3476_; 
lean_dec_ref(v_mctx_3470_);
lean_inc_ref(v_type_3445_);
v___x_3476_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3365_, v___f_3364_, v_type_3445_, v___x_3472_);
v___y_3465_ = v___x_3476_;
goto v___jp_3464_;
}
v___jp_3447_:
{
lean_object* v___x_3450_; lean_object* v_cache_3451_; lean_object* v_zetaDeltaFVarIds_3452_; lean_object* v_postponed_3453_; lean_object* v_diag_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3462_; 
v___x_3450_ = lean_st_ref_take(v___y_3341_);
v_cache_3451_ = lean_ctor_get(v___x_3450_, 1);
v_zetaDeltaFVarIds_3452_ = lean_ctor_get(v___x_3450_, 2);
v_postponed_3453_ = lean_ctor_get(v___x_3450_, 3);
v_diag_3454_ = lean_ctor_get(v___x_3450_, 4);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3463_);
v___x_3456_ = v___x_3450_;
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_diag_3454_);
lean_inc(v_postponed_3453_);
lean_inc(v_zetaDeltaFVarIds_3452_);
lean_inc(v_cache_3451_);
lean_dec(v___x_3450_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3462_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_mctx_3449_);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_mctx_3449_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_cache_3451_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_zetaDeltaFVarIds_3452_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_postponed_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_diag_3454_);
v___x_3459_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_st_ref_put(v___y_3341_, v___x_3459_);
v_a_3361_ = v_fst_3448_;
goto v___jp_3360_;
}
}
}
v___jp_3464_:
{
lean_object* v_snd_3466_; lean_object* v_fst_3467_; lean_object* v_mctx_3468_; uint8_t v___x_3469_; 
v_snd_3466_ = lean_ctor_get(v___y_3465_, 1);
lean_inc(v_snd_3466_);
v_fst_3467_ = lean_ctor_get(v___y_3465_, 0);
lean_inc(v_fst_3467_);
lean_dec_ref(v___y_3465_);
v_mctx_3468_ = lean_ctor_get(v_snd_3466_, 1);
lean_inc_ref(v_mctx_3468_);
lean_dec(v_snd_3466_);
v___x_3469_ = lean_unbox(v_fst_3467_);
lean_dec(v_fst_3467_);
v_fst_3448_ = v___x_3469_;
v_mctx_3449_ = v_mctx_3468_;
goto v___jp_3447_;
}
}
}
v___jp_3360_:
{
if (v_a_3361_ == 0)
{
v_a_3351_ = v_snd_3345_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = l_Lean_LocalDecl_fvarId(v_val_3359_);
v___x_3363_ = lean_array_push(v_snd_3345_, v___x_3362_);
v_a_3351_ = v___x_3363_;
goto v___jp_3350_;
}
}
}
v___jp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3351_);
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_a_3351_);
v___x_3353_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
size_t v___x_3354_; size_t v___x_3355_; 
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3339_, v___x_3354_);
v_i_3339_ = v___x_3355_;
v_b_3340_ = v___x_3353_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3479_, lean_object* v_sz_3480_, lean_object* v_i_3481_, lean_object* v_b_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
size_t v_sz_boxed_3485_; size_t v_i_boxed_3486_; lean_object* v_res_3487_; 
v_sz_boxed_3485_ = lean_unbox_usize(v_sz_3480_);
lean_dec(v_sz_3480_);
v_i_boxed_3486_ = lean_unbox_usize(v_i_3481_);
lean_dec(v_i_3481_);
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3479_, v_sz_boxed_3485_, v_i_boxed_3486_, v_b_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v_as_3479_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3488_, size_t v_sz_3489_, size_t v_i_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_usize_dec_lt(v_i_3490_, v_sz_3489_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_b_3491_);
return v___x_3498_;
}
else
{
lean_object* v_snd_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3631_; 
v_snd_3499_ = lean_ctor_get(v_b_3491_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_b_3491_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v_b_3491_, 0);
lean_dec(v_unused_3632_);
v___x_3501_ = v_b_3491_;
v_isShared_3502_ = v_isSharedCheck_3631_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_snd_3499_);
lean_dec(v_b_3491_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3631_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v_a_3505_; lean_object* v_a_3512_; 
v___x_3503_ = lean_box(0);
v_a_3512_ = lean_array_uget_borrowed(v_as_3488_, v_i_3490_);
if (lean_obj_tag(v_a_3512_) == 0)
{
v_a_3505_ = v_snd_3499_;
goto v___jp_3504_;
}
else
{
lean_object* v_val_3513_; uint8_t v_a_3515_; lean_object* v___f_3518_; lean_object* v___f_3519_; 
v_val_3513_ = lean_ctor_get(v_a_3512_, 0);
v___f_3518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3499_);
v___f_3519_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3519_, 0, v_snd_3499_);
if (lean_obj_tag(v_val_3513_) == 0)
{
lean_object* v_type_3520_; lean_object* v___x_3521_; uint8_t v_fst_3523_; lean_object* v_mctx_3524_; lean_object* v___y_3540_; lean_object* v_mctx_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_type_3520_ = lean_ctor_get(v_val_3513_, 3);
v___x_3521_ = lean_st_ref_get(v___y_3493_);
v_mctx_3545_ = lean_ctor_get(v___x_3521_, 0);
lean_inc_ref_n(v_mctx_3545_, 2);
lean_dec(v___x_3521_);
v___x_3546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v_mctx_3545_);
v___x_3548_ = l_Lean_Expr_hasFVar(v_type_3520_);
if (v___x_3548_ == 0)
{
uint8_t v___x_3549_; 
v___x_3549_ = l_Lean_Expr_hasMVar(v_type_3520_);
if (v___x_3549_ == 0)
{
lean_dec_ref_known(v___x_3547_, 2);
lean_dec_ref(v___f_3519_);
v_fst_3523_ = v___x_3549_;
v_mctx_3524_ = v_mctx_3545_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3550_; 
lean_dec_ref(v_mctx_3545_);
lean_inc_ref(v_type_3520_);
v___x_3550_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3520_, v___x_3547_);
v___y_3540_ = v___x_3550_;
goto v___jp_3539_;
}
}
else
{
lean_object* v___x_3551_; 
lean_dec_ref(v_mctx_3545_);
lean_inc_ref(v_type_3520_);
v___x_3551_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3520_, v___x_3547_);
v___y_3540_ = v___x_3551_;
goto v___jp_3539_;
}
v___jp_3522_:
{
lean_object* v___x_3525_; lean_object* v_cache_3526_; lean_object* v_zetaDeltaFVarIds_3527_; lean_object* v_postponed_3528_; lean_object* v_diag_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3537_; 
v___x_3525_ = lean_st_ref_take(v___y_3493_);
v_cache_3526_ = lean_ctor_get(v___x_3525_, 1);
v_zetaDeltaFVarIds_3527_ = lean_ctor_get(v___x_3525_, 2);
v_postponed_3528_ = lean_ctor_get(v___x_3525_, 3);
v_diag_3529_ = lean_ctor_get(v___x_3525_, 4);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v___x_3525_, 0);
lean_dec(v_unused_3538_);
v___x_3531_ = v___x_3525_;
v_isShared_3532_ = v_isSharedCheck_3537_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_diag_3529_);
lean_inc(v_postponed_3528_);
lean_inc(v_zetaDeltaFVarIds_3527_);
lean_inc(v_cache_3526_);
lean_dec(v___x_3525_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3537_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_mctx_3524_);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_mctx_3524_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_cache_3526_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_zetaDeltaFVarIds_3527_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v_postponed_3528_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_diag_3529_);
v___x_3534_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_st_ref_put(v___y_3493_, v___x_3534_);
v_a_3515_ = v_fst_3523_;
goto v___jp_3514_;
}
}
}
v___jp_3539_:
{
lean_object* v_snd_3541_; lean_object* v_fst_3542_; lean_object* v_mctx_3543_; uint8_t v___x_3544_; 
v_snd_3541_ = lean_ctor_get(v___y_3540_, 1);
lean_inc(v_snd_3541_);
v_fst_3542_ = lean_ctor_get(v___y_3540_, 0);
lean_inc(v_fst_3542_);
lean_dec_ref(v___y_3540_);
v_mctx_3543_ = lean_ctor_get(v_snd_3541_, 1);
lean_inc_ref(v_mctx_3543_);
lean_dec(v_snd_3541_);
v___x_3544_ = lean_unbox(v_fst_3542_);
lean_dec(v_fst_3542_);
v_fst_3523_ = v___x_3544_;
v_mctx_3524_ = v_mctx_3543_;
goto v___jp_3522_;
}
}
else
{
uint8_t v_nondep_3552_; 
v_nondep_3552_ = lean_ctor_get_uint8(v_val_3513_, sizeof(void*)*5);
if (v_nondep_3552_ == 0)
{
lean_object* v_type_3553_; lean_object* v_value_3554_; lean_object* v___x_3555_; uint8_t v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___y_3575_; lean_object* v_snd_3580_; lean_object* v___y_3586_; lean_object* v_mctx_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_type_3553_ = lean_ctor_get(v_val_3513_, 3);
v_value_3554_ = lean_ctor_get(v_val_3513_, 4);
v___x_3555_ = lean_st_ref_get(v___y_3493_);
v_mctx_3592_ = lean_ctor_get(v___x_3555_, 0);
lean_inc_ref(v_mctx_3592_);
lean_dec(v___x_3555_);
v___x_3593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_mctx_3592_);
v___x_3595_ = l_Lean_Expr_hasFVar(v_type_3553_);
if (v___x_3595_ == 0)
{
uint8_t v___x_3596_; 
v___x_3596_ = l_Lean_Expr_hasMVar(v_type_3553_);
if (v___x_3596_ == 0)
{
v_snd_3580_ = v___x_3594_;
goto v___jp_3579_;
}
else
{
lean_object* v___x_3597_; 
lean_inc_ref(v_type_3553_);
lean_inc_ref(v___f_3519_);
v___x_3597_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3553_, v___x_3594_);
v___y_3586_ = v___x_3597_;
goto v___jp_3585_;
}
}
else
{
lean_object* v___x_3598_; 
lean_inc_ref(v_type_3553_);
lean_inc_ref(v___f_3519_);
v___x_3598_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3553_, v___x_3594_);
v___y_3586_ = v___x_3598_;
goto v___jp_3585_;
}
v___jp_3556_:
{
lean_object* v_mctx_3559_; lean_object* v___x_3560_; lean_object* v_cache_3561_; lean_object* v_zetaDeltaFVarIds_3562_; lean_object* v_postponed_3563_; lean_object* v_diag_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3572_; 
v_mctx_3559_ = lean_ctor_get(v_snd_3558_, 1);
lean_inc_ref(v_mctx_3559_);
lean_dec_ref(v_snd_3558_);
v___x_3560_ = lean_st_ref_take(v___y_3493_);
v_cache_3561_ = lean_ctor_get(v___x_3560_, 1);
v_zetaDeltaFVarIds_3562_ = lean_ctor_get(v___x_3560_, 2);
v_postponed_3563_ = lean_ctor_get(v___x_3560_, 3);
v_diag_3564_ = lean_ctor_get(v___x_3560_, 4);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v___x_3560_, 0);
lean_dec(v_unused_3573_);
v___x_3566_ = v___x_3560_;
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_diag_3564_);
lean_inc(v_postponed_3563_);
lean_inc(v_zetaDeltaFVarIds_3562_);
lean_inc(v_cache_3561_);
lean_dec(v___x_3560_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3572_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v_mctx_3559_);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_mctx_3559_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_cache_3561_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_zetaDeltaFVarIds_3562_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_postponed_3563_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_diag_3564_);
v___x_3569_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_st_ref_put(v___y_3493_, v___x_3569_);
v_a_3515_ = v_fst_3557_;
goto v___jp_3514_;
}
}
}
v___jp_3574_:
{
lean_object* v_fst_3576_; lean_object* v_snd_3577_; uint8_t v___x_3578_; 
v_fst_3576_ = lean_ctor_get(v___y_3575_, 0);
lean_inc(v_fst_3576_);
v_snd_3577_ = lean_ctor_get(v___y_3575_, 1);
lean_inc(v_snd_3577_);
lean_dec_ref(v___y_3575_);
v___x_3578_ = lean_unbox(v_fst_3576_);
lean_dec(v_fst_3576_);
v_fst_3557_ = v___x_3578_;
v_snd_3558_ = v_snd_3577_;
goto v___jp_3556_;
}
v___jp_3579_:
{
uint8_t v___x_3581_; 
v___x_3581_ = l_Lean_Expr_hasFVar(v_value_3554_);
if (v___x_3581_ == 0)
{
uint8_t v___x_3582_; 
v___x_3582_ = l_Lean_Expr_hasMVar(v_value_3554_);
if (v___x_3582_ == 0)
{
lean_dec_ref(v___f_3519_);
v_fst_3557_ = v___x_3582_;
v_snd_3558_ = v_snd_3580_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3583_; 
lean_inc_ref(v_value_3554_);
v___x_3583_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_value_3554_, v_snd_3580_);
v___y_3575_ = v___x_3583_;
goto v___jp_3574_;
}
}
else
{
lean_object* v___x_3584_; 
lean_inc_ref(v_value_3554_);
v___x_3584_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_value_3554_, v_snd_3580_);
v___y_3575_ = v___x_3584_;
goto v___jp_3574_;
}
}
v___jp_3585_:
{
lean_object* v_fst_3587_; uint8_t v___x_3588_; 
v_fst_3587_ = lean_ctor_get(v___y_3586_, 0);
v___x_3588_ = lean_unbox(v_fst_3587_);
if (v___x_3588_ == 0)
{
lean_object* v_snd_3589_; 
v_snd_3589_ = lean_ctor_get(v___y_3586_, 1);
lean_inc(v_snd_3589_);
lean_dec_ref(v___y_3586_);
v_snd_3580_ = v_snd_3589_;
goto v___jp_3579_;
}
else
{
lean_object* v_snd_3590_; uint8_t v___x_3591_; 
lean_inc(v_fst_3587_);
lean_dec_ref(v___f_3519_);
v_snd_3590_ = lean_ctor_get(v___y_3586_, 1);
lean_inc(v_snd_3590_);
lean_dec_ref(v___y_3586_);
v___x_3591_ = lean_unbox(v_fst_3587_);
lean_dec(v_fst_3587_);
v_fst_3557_ = v___x_3591_;
v_snd_3558_ = v_snd_3590_;
goto v___jp_3556_;
}
}
}
else
{
lean_object* v_type_3599_; lean_object* v___x_3600_; uint8_t v_fst_3602_; lean_object* v_mctx_3603_; lean_object* v___y_3619_; lean_object* v_mctx_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v_type_3599_ = lean_ctor_get(v_val_3513_, 3);
v___x_3600_ = lean_st_ref_get(v___y_3493_);
v_mctx_3624_ = lean_ctor_get(v___x_3600_, 0);
lean_inc_ref_n(v_mctx_3624_, 2);
lean_dec(v___x_3600_);
v___x_3625_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v_mctx_3624_);
v___x_3627_ = l_Lean_Expr_hasFVar(v_type_3599_);
if (v___x_3627_ == 0)
{
uint8_t v___x_3628_; 
v___x_3628_ = l_Lean_Expr_hasMVar(v_type_3599_);
if (v___x_3628_ == 0)
{
lean_dec_ref_known(v___x_3626_, 2);
lean_dec_ref(v___f_3519_);
v_fst_3602_ = v___x_3628_;
v_mctx_3603_ = v_mctx_3624_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3629_; 
lean_dec_ref(v_mctx_3624_);
lean_inc_ref(v_type_3599_);
v___x_3629_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3599_, v___x_3626_);
v___y_3619_ = v___x_3629_;
goto v___jp_3618_;
}
}
else
{
lean_object* v___x_3630_; 
lean_dec_ref(v_mctx_3624_);
lean_inc_ref(v_type_3599_);
v___x_3630_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3519_, v___f_3518_, v_type_3599_, v___x_3626_);
v___y_3619_ = v___x_3630_;
goto v___jp_3618_;
}
v___jp_3601_:
{
lean_object* v___x_3604_; lean_object* v_cache_3605_; lean_object* v_zetaDeltaFVarIds_3606_; lean_object* v_postponed_3607_; lean_object* v_diag_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3616_; 
v___x_3604_ = lean_st_ref_take(v___y_3493_);
v_cache_3605_ = lean_ctor_get(v___x_3604_, 1);
v_zetaDeltaFVarIds_3606_ = lean_ctor_get(v___x_3604_, 2);
v_postponed_3607_ = lean_ctor_get(v___x_3604_, 3);
v_diag_3608_ = lean_ctor_get(v___x_3604_, 4);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3617_);
v___x_3610_ = v___x_3604_;
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_diag_3608_);
lean_inc(v_postponed_3607_);
lean_inc(v_zetaDeltaFVarIds_3606_);
lean_inc(v_cache_3605_);
lean_dec(v___x_3604_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v_mctx_3603_);
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_mctx_3603_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_cache_3605_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v_zetaDeltaFVarIds_3606_);
lean_ctor_set(v_reuseFailAlloc_3615_, 3, v_postponed_3607_);
lean_ctor_set(v_reuseFailAlloc_3615_, 4, v_diag_3608_);
v___x_3613_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_st_ref_put(v___y_3493_, v___x_3613_);
v_a_3515_ = v_fst_3602_;
goto v___jp_3514_;
}
}
}
v___jp_3618_:
{
lean_object* v_snd_3620_; lean_object* v_fst_3621_; lean_object* v_mctx_3622_; uint8_t v___x_3623_; 
v_snd_3620_ = lean_ctor_get(v___y_3619_, 1);
lean_inc(v_snd_3620_);
v_fst_3621_ = lean_ctor_get(v___y_3619_, 0);
lean_inc(v_fst_3621_);
lean_dec_ref(v___y_3619_);
v_mctx_3622_ = lean_ctor_get(v_snd_3620_, 1);
lean_inc_ref(v_mctx_3622_);
lean_dec(v_snd_3620_);
v___x_3623_ = lean_unbox(v_fst_3621_);
lean_dec(v_fst_3621_);
v_fst_3602_ = v___x_3623_;
v_mctx_3603_ = v_mctx_3622_;
goto v___jp_3601_;
}
}
}
v___jp_3514_:
{
if (v_a_3515_ == 0)
{
v_a_3505_ = v_snd_3499_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = l_Lean_LocalDecl_fvarId(v_val_3513_);
v___x_3517_ = lean_array_push(v_snd_3499_, v___x_3516_);
v_a_3505_ = v___x_3517_;
goto v___jp_3504_;
}
}
}
v___jp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_a_3505_);
lean_ctor_set(v___x_3501_, 0, v___x_3503_);
v___x_3507_ = v___x_3501_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3505_);
v___x_3507_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3490_, v___x_3508_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3488_, v_sz_3489_, v___x_3509_, v___x_3507_, v___y_3493_);
return v___x_3510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3633_, lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
size_t v_sz_boxed_3642_; size_t v_i_boxed_3643_; lean_object* v_res_3644_; 
v_sz_boxed_3642_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3643_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3633_, v_sz_boxed_3642_, v_i_boxed_3643_, v_b_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_as_3633_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3645_, lean_object* v_n_3646_, lean_object* v_b_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
if (lean_obj_tag(v_n_3646_) == 0)
{
lean_object* v_cs_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; size_t v_sz_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
v_cs_3653_ = lean_ctor_get(v_n_3646_, 0);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v_b_3647_);
v_sz_3656_ = lean_array_size(v_cs_3653_);
v___x_3657_ = ((size_t)0ULL);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3645_, v_cs_3653_, v_sz_3656_, v___x_3657_, v___x_3655_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3673_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3673_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3673_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v_fst_3663_; 
v_fst_3663_ = lean_ctor_get(v_a_3659_, 0);
if (lean_obj_tag(v_fst_3663_) == 0)
{
lean_object* v_snd_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v_snd_3664_ = lean_ctor_get(v_a_3659_, 1);
lean_inc(v_snd_3664_);
lean_dec(v_a_3659_);
v___x_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3665_, 0, v_snd_3664_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3665_);
v___x_3667_ = v___x_3661_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
else
{
lean_object* v_val_3669_; lean_object* v___x_3671_; 
lean_inc_ref(v_fst_3663_);
lean_dec(v_a_3659_);
v_val_3669_ = lean_ctor_get(v_fst_3663_, 0);
lean_inc(v_val_3669_);
lean_dec_ref_known(v_fst_3663_, 1);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v_val_3669_);
v___x_3671_ = v___x_3661_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_val_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
v_a_3674_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3658_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3658_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_vs_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; size_t v_sz_3685_; size_t v___x_3686_; lean_object* v___x_3687_; 
v_vs_3682_ = lean_ctor_get(v_n_3646_, 0);
v___x_3683_ = lean_box(0);
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
lean_ctor_set(v___x_3684_, 1, v_b_3647_);
v_sz_3685_ = lean_array_size(v_vs_3682_);
v___x_3686_ = ((size_t)0ULL);
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3682_, v_sz_3685_, v___x_3686_, v___x_3684_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3702_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3690_ = v___x_3687_;
v_isShared_3691_ = v_isSharedCheck_3702_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3687_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3702_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_fst_3692_; 
v_fst_3692_ = lean_ctor_get(v_a_3688_, 0);
if (lean_obj_tag(v_fst_3692_) == 0)
{
lean_object* v_snd_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v_snd_3693_ = lean_ctor_get(v_a_3688_, 1);
lean_inc(v_snd_3693_);
lean_dec(v_a_3688_);
v___x_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3694_, 0, v_snd_3693_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3694_);
v___x_3696_ = v___x_3690_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
else
{
lean_object* v_val_3698_; lean_object* v___x_3700_; 
lean_inc_ref(v_fst_3692_);
lean_dec(v_a_3688_);
v_val_3698_ = lean_ctor_get(v_fst_3692_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v_fst_3692_, 1);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v_val_3698_);
v___x_3700_ = v___x_3690_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_val_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v_a_3703_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3687_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3687_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3711_, lean_object* v_as_3712_, size_t v_sz_3713_, size_t v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_usize_dec_lt(v_i_3714_, v_sz_3713_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v_b_3715_);
return v___x_3722_;
}
else
{
lean_object* v_snd_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3757_; 
v_snd_3723_ = lean_ctor_get(v_b_3715_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_b_3715_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v_b_3715_, 0);
lean_dec(v_unused_3758_);
v___x_3725_ = v_b_3715_;
v_isShared_3726_ = v_isSharedCheck_3757_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_snd_3723_);
lean_dec(v_b_3715_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3757_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v_a_3728_; lean_object* v___x_3729_; 
v___x_3727_ = lean_box(0);
v_a_3728_ = lean_array_uget_borrowed(v_as_3712_, v_i_3714_);
lean_inc(v_snd_3723_);
v___x_3729_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3711_, v_a_3728_, v_snd_3723_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3748_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3748_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3748_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
if (lean_obj_tag(v_a_3730_) == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_a_3730_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3734_);
v___x_3736_ = v___x_3725_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_snd_3723_);
v___x_3736_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; 
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3736_);
v___x_3738_ = v___x_3732_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; 
lean_del_object(v___x_3732_);
lean_dec(v_snd_3723_);
v_a_3741_ = lean_ctor_get(v_a_3730_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v_a_3730_, 1);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 1, v_a_3741_);
lean_ctor_set(v___x_3725_, 0, v___x_3727_);
v___x_3743_ = v___x_3725_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_a_3741_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
size_t v___x_3744_; size_t v___x_3745_; 
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_add(v_i_3714_, v___x_3744_);
v_i_3714_ = v___x_3745_;
v_b_3715_ = v___x_3743_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_del_object(v___x_3725_);
lean_dec(v_snd_3723_);
v_a_3749_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3729_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3729_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3759_, lean_object* v_as_3760_, lean_object* v_sz_3761_, lean_object* v_i_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
size_t v_sz_boxed_3769_; size_t v_i_boxed_3770_; lean_object* v_res_3771_; 
v_sz_boxed_3769_ = lean_unbox_usize(v_sz_3761_);
lean_dec(v_sz_3761_);
v_i_boxed_3770_ = lean_unbox_usize(v_i_3762_);
lean_dec(v_i_3762_);
v_res_3771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3759_, v_as_3760_, v_sz_boxed_3769_, v_i_boxed_3770_, v_b_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_as_3760_);
lean_dec_ref(v_init_3759_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3772_, lean_object* v_n_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3772_, v_n_3773_, v_b_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v_n_3773_);
lean_dec_ref(v_init_3772_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3781_, size_t v_sz_3782_, size_t v_i_3783_, lean_object* v_b_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_usize_dec_lt(v_i_3783_, v_sz_3782_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_b_3784_);
return v___x_3788_;
}
else
{
lean_object* v_snd_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3921_; 
v_snd_3789_ = lean_ctor_get(v_b_3784_, 1);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_b_3784_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; 
v_unused_3922_ = lean_ctor_get(v_b_3784_, 0);
lean_dec(v_unused_3922_);
v___x_3791_ = v_b_3784_;
v_isShared_3792_ = v_isSharedCheck_3921_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_snd_3789_);
lean_dec(v_b_3784_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3921_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v_a_3795_; lean_object* v_a_3802_; 
v___x_3793_ = lean_box(0);
v_a_3802_ = lean_array_uget_borrowed(v_as_3781_, v_i_3783_);
if (lean_obj_tag(v_a_3802_) == 0)
{
v_a_3795_ = v_snd_3789_;
goto v___jp_3794_;
}
else
{
lean_object* v_val_3803_; uint8_t v_a_3805_; lean_object* v___f_3808_; lean_object* v___f_3809_; 
v_val_3803_ = lean_ctor_get(v_a_3802_, 0);
v___f_3808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3789_);
v___f_3809_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3809_, 0, v_snd_3789_);
if (lean_obj_tag(v_val_3803_) == 0)
{
lean_object* v_type_3810_; lean_object* v___x_3811_; uint8_t v_fst_3813_; lean_object* v_mctx_3814_; lean_object* v___y_3830_; lean_object* v_mctx_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_type_3810_ = lean_ctor_get(v_val_3803_, 3);
v___x_3811_ = lean_st_ref_get(v___y_3785_);
v_mctx_3835_ = lean_ctor_get(v___x_3811_, 0);
lean_inc_ref_n(v_mctx_3835_, 2);
lean_dec(v___x_3811_);
v___x_3836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
lean_ctor_set(v___x_3837_, 1, v_mctx_3835_);
v___x_3838_ = l_Lean_Expr_hasFVar(v_type_3810_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
v___x_3839_ = l_Lean_Expr_hasMVar(v_type_3810_);
if (v___x_3839_ == 0)
{
lean_dec_ref_known(v___x_3837_, 2);
lean_dec_ref(v___f_3809_);
v_fst_3813_ = v___x_3839_;
v_mctx_3814_ = v_mctx_3835_;
goto v___jp_3812_;
}
else
{
lean_object* v___x_3840_; 
lean_dec_ref(v_mctx_3835_);
lean_inc_ref(v_type_3810_);
v___x_3840_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3810_, v___x_3837_);
v___y_3830_ = v___x_3840_;
goto v___jp_3829_;
}
}
else
{
lean_object* v___x_3841_; 
lean_dec_ref(v_mctx_3835_);
lean_inc_ref(v_type_3810_);
v___x_3841_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3810_, v___x_3837_);
v___y_3830_ = v___x_3841_;
goto v___jp_3829_;
}
v___jp_3812_:
{
lean_object* v___x_3815_; lean_object* v_cache_3816_; lean_object* v_zetaDeltaFVarIds_3817_; lean_object* v_postponed_3818_; lean_object* v_diag_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3827_; 
v___x_3815_ = lean_st_ref_take(v___y_3785_);
v_cache_3816_ = lean_ctor_get(v___x_3815_, 1);
v_zetaDeltaFVarIds_3817_ = lean_ctor_get(v___x_3815_, 2);
v_postponed_3818_ = lean_ctor_get(v___x_3815_, 3);
v_diag_3819_ = lean_ctor_get(v___x_3815_, 4);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v___x_3815_, 0);
lean_dec(v_unused_3828_);
v___x_3821_ = v___x_3815_;
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_diag_3819_);
lean_inc(v_postponed_3818_);
lean_inc(v_zetaDeltaFVarIds_3817_);
lean_inc(v_cache_3816_);
lean_dec(v___x_3815_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_mctx_3814_);
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_mctx_3814_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_cache_3816_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_zetaDeltaFVarIds_3817_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v_postponed_3818_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v_diag_3819_);
v___x_3824_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_st_ref_put(v___y_3785_, v___x_3824_);
v_a_3805_ = v_fst_3813_;
goto v___jp_3804_;
}
}
}
v___jp_3829_:
{
lean_object* v_snd_3831_; lean_object* v_fst_3832_; lean_object* v_mctx_3833_; uint8_t v___x_3834_; 
v_snd_3831_ = lean_ctor_get(v___y_3830_, 1);
lean_inc(v_snd_3831_);
v_fst_3832_ = lean_ctor_get(v___y_3830_, 0);
lean_inc(v_fst_3832_);
lean_dec_ref(v___y_3830_);
v_mctx_3833_ = lean_ctor_get(v_snd_3831_, 1);
lean_inc_ref(v_mctx_3833_);
lean_dec(v_snd_3831_);
v___x_3834_ = lean_unbox(v_fst_3832_);
lean_dec(v_fst_3832_);
v_fst_3813_ = v___x_3834_;
v_mctx_3814_ = v_mctx_3833_;
goto v___jp_3812_;
}
}
else
{
uint8_t v_nondep_3842_; 
v_nondep_3842_ = lean_ctor_get_uint8(v_val_3803_, sizeof(void*)*5);
if (v_nondep_3842_ == 0)
{
lean_object* v_type_3843_; lean_object* v_value_3844_; lean_object* v___x_3845_; uint8_t v_fst_3847_; lean_object* v_snd_3848_; lean_object* v___y_3865_; lean_object* v_snd_3870_; lean_object* v___y_3876_; lean_object* v_mctx_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v_type_3843_ = lean_ctor_get(v_val_3803_, 3);
v_value_3844_ = lean_ctor_get(v_val_3803_, 4);
v___x_3845_ = lean_st_ref_get(v___y_3785_);
v_mctx_3882_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_mctx_3882_);
lean_dec(v___x_3845_);
v___x_3883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
lean_ctor_set(v___x_3884_, 1, v_mctx_3882_);
v___x_3885_ = l_Lean_Expr_hasFVar(v_type_3843_);
if (v___x_3885_ == 0)
{
uint8_t v___x_3886_; 
v___x_3886_ = l_Lean_Expr_hasMVar(v_type_3843_);
if (v___x_3886_ == 0)
{
v_snd_3870_ = v___x_3884_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3887_; 
lean_inc_ref(v_type_3843_);
lean_inc_ref(v___f_3809_);
v___x_3887_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3843_, v___x_3884_);
v___y_3876_ = v___x_3887_;
goto v___jp_3875_;
}
}
else
{
lean_object* v___x_3888_; 
lean_inc_ref(v_type_3843_);
lean_inc_ref(v___f_3809_);
v___x_3888_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3843_, v___x_3884_);
v___y_3876_ = v___x_3888_;
goto v___jp_3875_;
}
v___jp_3846_:
{
lean_object* v_mctx_3849_; lean_object* v___x_3850_; lean_object* v_cache_3851_; lean_object* v_zetaDeltaFVarIds_3852_; lean_object* v_postponed_3853_; lean_object* v_diag_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3862_; 
v_mctx_3849_ = lean_ctor_get(v_snd_3848_, 1);
lean_inc_ref(v_mctx_3849_);
lean_dec_ref(v_snd_3848_);
v___x_3850_ = lean_st_ref_take(v___y_3785_);
v_cache_3851_ = lean_ctor_get(v___x_3850_, 1);
v_zetaDeltaFVarIds_3852_ = lean_ctor_get(v___x_3850_, 2);
v_postponed_3853_ = lean_ctor_get(v___x_3850_, 3);
v_diag_3854_ = lean_ctor_get(v___x_3850_, 4);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; 
v_unused_3863_ = lean_ctor_get(v___x_3850_, 0);
lean_dec(v_unused_3863_);
v___x_3856_ = v___x_3850_;
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_diag_3854_);
lean_inc(v_postponed_3853_);
lean_inc(v_zetaDeltaFVarIds_3852_);
lean_inc(v_cache_3851_);
lean_dec(v___x_3850_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_mctx_3849_);
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_mctx_3849_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_cache_3851_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_zetaDeltaFVarIds_3852_);
lean_ctor_set(v_reuseFailAlloc_3861_, 3, v_postponed_3853_);
lean_ctor_set(v_reuseFailAlloc_3861_, 4, v_diag_3854_);
v___x_3859_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_st_ref_put(v___y_3785_, v___x_3859_);
v_a_3805_ = v_fst_3847_;
goto v___jp_3804_;
}
}
}
v___jp_3864_:
{
lean_object* v_fst_3866_; lean_object* v_snd_3867_; uint8_t v___x_3868_; 
v_fst_3866_ = lean_ctor_get(v___y_3865_, 0);
lean_inc(v_fst_3866_);
v_snd_3867_ = lean_ctor_get(v___y_3865_, 1);
lean_inc(v_snd_3867_);
lean_dec_ref(v___y_3865_);
v___x_3868_ = lean_unbox(v_fst_3866_);
lean_dec(v_fst_3866_);
v_fst_3847_ = v___x_3868_;
v_snd_3848_ = v_snd_3867_;
goto v___jp_3846_;
}
v___jp_3869_:
{
uint8_t v___x_3871_; 
v___x_3871_ = l_Lean_Expr_hasFVar(v_value_3844_);
if (v___x_3871_ == 0)
{
uint8_t v___x_3872_; 
v___x_3872_ = l_Lean_Expr_hasMVar(v_value_3844_);
if (v___x_3872_ == 0)
{
lean_dec_ref(v___f_3809_);
v_fst_3847_ = v___x_3872_;
v_snd_3848_ = v_snd_3870_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3873_; 
lean_inc_ref(v_value_3844_);
v___x_3873_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_value_3844_, v_snd_3870_);
v___y_3865_ = v___x_3873_;
goto v___jp_3864_;
}
}
else
{
lean_object* v___x_3874_; 
lean_inc_ref(v_value_3844_);
v___x_3874_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_value_3844_, v_snd_3870_);
v___y_3865_ = v___x_3874_;
goto v___jp_3864_;
}
}
v___jp_3875_:
{
lean_object* v_fst_3877_; uint8_t v___x_3878_; 
v_fst_3877_ = lean_ctor_get(v___y_3876_, 0);
v___x_3878_ = lean_unbox(v_fst_3877_);
if (v___x_3878_ == 0)
{
lean_object* v_snd_3879_; 
v_snd_3879_ = lean_ctor_get(v___y_3876_, 1);
lean_inc(v_snd_3879_);
lean_dec_ref(v___y_3876_);
v_snd_3870_ = v_snd_3879_;
goto v___jp_3869_;
}
else
{
lean_object* v_snd_3880_; uint8_t v___x_3881_; 
lean_inc(v_fst_3877_);
lean_dec_ref(v___f_3809_);
v_snd_3880_ = lean_ctor_get(v___y_3876_, 1);
lean_inc(v_snd_3880_);
lean_dec_ref(v___y_3876_);
v___x_3881_ = lean_unbox(v_fst_3877_);
lean_dec(v_fst_3877_);
v_fst_3847_ = v___x_3881_;
v_snd_3848_ = v_snd_3880_;
goto v___jp_3846_;
}
}
}
else
{
lean_object* v_type_3889_; lean_object* v___x_3890_; uint8_t v_fst_3892_; lean_object* v_mctx_3893_; lean_object* v___y_3909_; lean_object* v_mctx_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v_type_3889_ = lean_ctor_get(v_val_3803_, 3);
v___x_3890_ = lean_st_ref_get(v___y_3785_);
v_mctx_3914_ = lean_ctor_get(v___x_3890_, 0);
lean_inc_ref_n(v_mctx_3914_, 2);
lean_dec(v___x_3890_);
v___x_3915_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v_mctx_3914_);
v___x_3917_ = l_Lean_Expr_hasFVar(v_type_3889_);
if (v___x_3917_ == 0)
{
uint8_t v___x_3918_; 
v___x_3918_ = l_Lean_Expr_hasMVar(v_type_3889_);
if (v___x_3918_ == 0)
{
lean_dec_ref_known(v___x_3916_, 2);
lean_dec_ref(v___f_3809_);
v_fst_3892_ = v___x_3918_;
v_mctx_3893_ = v_mctx_3914_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3919_; 
lean_dec_ref(v_mctx_3914_);
lean_inc_ref(v_type_3889_);
v___x_3919_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3889_, v___x_3916_);
v___y_3909_ = v___x_3919_;
goto v___jp_3908_;
}
}
else
{
lean_object* v___x_3920_; 
lean_dec_ref(v_mctx_3914_);
lean_inc_ref(v_type_3889_);
v___x_3920_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3809_, v___f_3808_, v_type_3889_, v___x_3916_);
v___y_3909_ = v___x_3920_;
goto v___jp_3908_;
}
v___jp_3891_:
{
lean_object* v___x_3894_; lean_object* v_cache_3895_; lean_object* v_zetaDeltaFVarIds_3896_; lean_object* v_postponed_3897_; lean_object* v_diag_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3906_; 
v___x_3894_ = lean_st_ref_take(v___y_3785_);
v_cache_3895_ = lean_ctor_get(v___x_3894_, 1);
v_zetaDeltaFVarIds_3896_ = lean_ctor_get(v___x_3894_, 2);
v_postponed_3897_ = lean_ctor_get(v___x_3894_, 3);
v_diag_3898_ = lean_ctor_get(v___x_3894_, 4);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; 
v_unused_3907_ = lean_ctor_get(v___x_3894_, 0);
lean_dec(v_unused_3907_);
v___x_3900_ = v___x_3894_;
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_diag_3898_);
lean_inc(v_postponed_3897_);
lean_inc(v_zetaDeltaFVarIds_3896_);
lean_inc(v_cache_3895_);
lean_dec(v___x_3894_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v_mctx_3893_);
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_mctx_3893_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_cache_3895_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_zetaDeltaFVarIds_3896_);
lean_ctor_set(v_reuseFailAlloc_3905_, 3, v_postponed_3897_);
lean_ctor_set(v_reuseFailAlloc_3905_, 4, v_diag_3898_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_st_ref_put(v___y_3785_, v___x_3903_);
v_a_3805_ = v_fst_3892_;
goto v___jp_3804_;
}
}
}
v___jp_3908_:
{
lean_object* v_snd_3910_; lean_object* v_fst_3911_; lean_object* v_mctx_3912_; uint8_t v___x_3913_; 
v_snd_3910_ = lean_ctor_get(v___y_3909_, 1);
lean_inc(v_snd_3910_);
v_fst_3911_ = lean_ctor_get(v___y_3909_, 0);
lean_inc(v_fst_3911_);
lean_dec_ref(v___y_3909_);
v_mctx_3912_ = lean_ctor_get(v_snd_3910_, 1);
lean_inc_ref(v_mctx_3912_);
lean_dec(v_snd_3910_);
v___x_3913_ = lean_unbox(v_fst_3911_);
lean_dec(v_fst_3911_);
v_fst_3892_ = v___x_3913_;
v_mctx_3893_ = v_mctx_3912_;
goto v___jp_3891_;
}
}
}
v___jp_3804_:
{
if (v_a_3805_ == 0)
{
v_a_3795_ = v_snd_3789_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = l_Lean_LocalDecl_fvarId(v_val_3803_);
v___x_3807_ = lean_array_push(v_snd_3789_, v___x_3806_);
v_a_3795_ = v___x_3807_;
goto v___jp_3794_;
}
}
}
v___jp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 1, v_a_3795_);
lean_ctor_set(v___x_3791_, 0, v___x_3793_);
v___x_3797_ = v___x_3791_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_a_3795_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
size_t v___x_3798_; size_t v___x_3799_; 
v___x_3798_ = ((size_t)1ULL);
v___x_3799_ = lean_usize_add(v_i_3783_, v___x_3798_);
v_i_3783_ = v___x_3799_;
v_b_3784_ = v___x_3797_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3923_, lean_object* v_sz_3924_, lean_object* v_i_3925_, lean_object* v_b_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
size_t v_sz_boxed_3929_; size_t v_i_boxed_3930_; lean_object* v_res_3931_; 
v_sz_boxed_3929_ = lean_unbox_usize(v_sz_3924_);
lean_dec(v_sz_3924_);
v_i_boxed_3930_ = lean_unbox_usize(v_i_3925_);
lean_dec(v_i_3925_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3923_, v_sz_boxed_3929_, v_i_boxed_3930_, v_b_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v_as_3923_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3932_, size_t v_sz_3933_, size_t v_i_3934_, lean_object* v_b_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
uint8_t v___x_3941_; 
v___x_3941_ = lean_usize_dec_lt(v_i_3934_, v_sz_3933_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; 
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_b_3935_);
return v___x_3942_;
}
else
{
lean_object* v_snd_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_4075_; 
v_snd_3943_ = lean_ctor_get(v_b_3935_, 1);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_b_3935_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v_b_3935_, 0);
lean_dec(v_unused_4076_);
v___x_3945_ = v_b_3935_;
v_isShared_3946_ = v_isSharedCheck_4075_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snd_3943_);
lean_dec(v_b_3935_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_4075_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v_a_3949_; lean_object* v_a_3956_; 
v___x_3947_ = lean_box(0);
v_a_3956_ = lean_array_uget_borrowed(v_as_3932_, v_i_3934_);
if (lean_obj_tag(v_a_3956_) == 0)
{
v_a_3949_ = v_snd_3943_;
goto v___jp_3948_;
}
else
{
lean_object* v_val_3957_; uint8_t v_a_3959_; lean_object* v___f_3962_; lean_object* v___f_3963_; 
v_val_3957_ = lean_ctor_get(v_a_3956_, 0);
v___f_3962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3943_);
v___f_3963_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3963_, 0, v_snd_3943_);
if (lean_obj_tag(v_val_3957_) == 0)
{
lean_object* v_type_3964_; lean_object* v___x_3965_; uint8_t v_fst_3967_; lean_object* v_mctx_3968_; lean_object* v___y_3984_; lean_object* v_mctx_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_type_3964_ = lean_ctor_get(v_val_3957_, 3);
v___x_3965_ = lean_st_ref_get(v___y_3937_);
v_mctx_3989_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref_n(v_mctx_3989_, 2);
lean_dec(v___x_3965_);
v___x_3990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v_mctx_3989_);
v___x_3992_ = l_Lean_Expr_hasFVar(v_type_3964_);
if (v___x_3992_ == 0)
{
uint8_t v___x_3993_; 
v___x_3993_ = l_Lean_Expr_hasMVar(v_type_3964_);
if (v___x_3993_ == 0)
{
lean_dec_ref_known(v___x_3991_, 2);
lean_dec_ref(v___f_3963_);
v_fst_3967_ = v___x_3993_;
v_mctx_3968_ = v_mctx_3989_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_3994_; 
lean_dec_ref(v_mctx_3989_);
lean_inc_ref(v_type_3964_);
v___x_3994_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_3964_, v___x_3991_);
v___y_3984_ = v___x_3994_;
goto v___jp_3983_;
}
}
else
{
lean_object* v___x_3995_; 
lean_dec_ref(v_mctx_3989_);
lean_inc_ref(v_type_3964_);
v___x_3995_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_3964_, v___x_3991_);
v___y_3984_ = v___x_3995_;
goto v___jp_3983_;
}
v___jp_3966_:
{
lean_object* v___x_3969_; lean_object* v_cache_3970_; lean_object* v_zetaDeltaFVarIds_3971_; lean_object* v_postponed_3972_; lean_object* v_diag_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3981_; 
v___x_3969_ = lean_st_ref_take(v___y_3937_);
v_cache_3970_ = lean_ctor_get(v___x_3969_, 1);
v_zetaDeltaFVarIds_3971_ = lean_ctor_get(v___x_3969_, 2);
v_postponed_3972_ = lean_ctor_get(v___x_3969_, 3);
v_diag_3973_ = lean_ctor_get(v___x_3969_, 4);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; 
v_unused_3982_ = lean_ctor_get(v___x_3969_, 0);
lean_dec(v_unused_3982_);
v___x_3975_ = v___x_3969_;
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_diag_3973_);
lean_inc(v_postponed_3972_);
lean_inc(v_zetaDeltaFVarIds_3971_);
lean_inc(v_cache_3970_);
lean_dec(v___x_3969_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v_mctx_3968_);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_mctx_3968_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_cache_3970_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_zetaDeltaFVarIds_3971_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_postponed_3972_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_diag_3973_);
v___x_3978_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_st_ref_put(v___y_3937_, v___x_3978_);
v_a_3959_ = v_fst_3967_;
goto v___jp_3958_;
}
}
}
v___jp_3983_:
{
lean_object* v_snd_3985_; lean_object* v_fst_3986_; lean_object* v_mctx_3987_; uint8_t v___x_3988_; 
v_snd_3985_ = lean_ctor_get(v___y_3984_, 1);
lean_inc(v_snd_3985_);
v_fst_3986_ = lean_ctor_get(v___y_3984_, 0);
lean_inc(v_fst_3986_);
lean_dec_ref(v___y_3984_);
v_mctx_3987_ = lean_ctor_get(v_snd_3985_, 1);
lean_inc_ref(v_mctx_3987_);
lean_dec(v_snd_3985_);
v___x_3988_ = lean_unbox(v_fst_3986_);
lean_dec(v_fst_3986_);
v_fst_3967_ = v___x_3988_;
v_mctx_3968_ = v_mctx_3987_;
goto v___jp_3966_;
}
}
else
{
uint8_t v_nondep_3996_; 
v_nondep_3996_ = lean_ctor_get_uint8(v_val_3957_, sizeof(void*)*5);
if (v_nondep_3996_ == 0)
{
lean_object* v_type_3997_; lean_object* v_value_3998_; lean_object* v___x_3999_; uint8_t v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___y_4019_; lean_object* v_snd_4024_; lean_object* v___y_4030_; lean_object* v_mctx_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; 
v_type_3997_ = lean_ctor_get(v_val_3957_, 3);
v_value_3998_ = lean_ctor_get(v_val_3957_, 4);
v___x_3999_ = lean_st_ref_get(v___y_3937_);
v_mctx_4036_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_ref(v_mctx_4036_);
lean_dec(v___x_3999_);
v___x_4037_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v_mctx_4036_);
v___x_4039_ = l_Lean_Expr_hasFVar(v_type_3997_);
if (v___x_4039_ == 0)
{
uint8_t v___x_4040_; 
v___x_4040_ = l_Lean_Expr_hasMVar(v_type_3997_);
if (v___x_4040_ == 0)
{
v_snd_4024_ = v___x_4038_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4041_; 
lean_inc_ref(v_type_3997_);
lean_inc_ref(v___f_3963_);
v___x_4041_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_3997_, v___x_4038_);
v___y_4030_ = v___x_4041_;
goto v___jp_4029_;
}
}
else
{
lean_object* v___x_4042_; 
lean_inc_ref(v_type_3997_);
lean_inc_ref(v___f_3963_);
v___x_4042_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_3997_, v___x_4038_);
v___y_4030_ = v___x_4042_;
goto v___jp_4029_;
}
v___jp_4000_:
{
lean_object* v_mctx_4003_; lean_object* v___x_4004_; lean_object* v_cache_4005_; lean_object* v_zetaDeltaFVarIds_4006_; lean_object* v_postponed_4007_; lean_object* v_diag_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4016_; 
v_mctx_4003_ = lean_ctor_get(v_snd_4002_, 1);
lean_inc_ref(v_mctx_4003_);
lean_dec_ref(v_snd_4002_);
v___x_4004_ = lean_st_ref_take(v___y_3937_);
v_cache_4005_ = lean_ctor_get(v___x_4004_, 1);
v_zetaDeltaFVarIds_4006_ = lean_ctor_get(v___x_4004_, 2);
v_postponed_4007_ = lean_ctor_get(v___x_4004_, 3);
v_diag_4008_ = lean_ctor_get(v___x_4004_, 4);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v___x_4004_, 0);
lean_dec(v_unused_4017_);
v___x_4010_ = v___x_4004_;
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_diag_4008_);
lean_inc(v_postponed_4007_);
lean_inc(v_zetaDeltaFVarIds_4006_);
lean_inc(v_cache_4005_);
lean_dec(v___x_4004_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v_mctx_4003_);
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_mctx_4003_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_cache_4005_);
lean_ctor_set(v_reuseFailAlloc_4015_, 2, v_zetaDeltaFVarIds_4006_);
lean_ctor_set(v_reuseFailAlloc_4015_, 3, v_postponed_4007_);
lean_ctor_set(v_reuseFailAlloc_4015_, 4, v_diag_4008_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_st_ref_put(v___y_3937_, v___x_4013_);
v_a_3959_ = v_fst_4001_;
goto v___jp_3958_;
}
}
}
v___jp_4018_:
{
lean_object* v_fst_4020_; lean_object* v_snd_4021_; uint8_t v___x_4022_; 
v_fst_4020_ = lean_ctor_get(v___y_4019_, 0);
lean_inc(v_fst_4020_);
v_snd_4021_ = lean_ctor_get(v___y_4019_, 1);
lean_inc(v_snd_4021_);
lean_dec_ref(v___y_4019_);
v___x_4022_ = lean_unbox(v_fst_4020_);
lean_dec(v_fst_4020_);
v_fst_4001_ = v___x_4022_;
v_snd_4002_ = v_snd_4021_;
goto v___jp_4000_;
}
v___jp_4023_:
{
uint8_t v___x_4025_; 
v___x_4025_ = l_Lean_Expr_hasFVar(v_value_3998_);
if (v___x_4025_ == 0)
{
uint8_t v___x_4026_; 
v___x_4026_ = l_Lean_Expr_hasMVar(v_value_3998_);
if (v___x_4026_ == 0)
{
lean_dec_ref(v___f_3963_);
v_fst_4001_ = v___x_4026_;
v_snd_4002_ = v_snd_4024_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4027_; 
lean_inc_ref(v_value_3998_);
v___x_4027_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_value_3998_, v_snd_4024_);
v___y_4019_ = v___x_4027_;
goto v___jp_4018_;
}
}
else
{
lean_object* v___x_4028_; 
lean_inc_ref(v_value_3998_);
v___x_4028_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_value_3998_, v_snd_4024_);
v___y_4019_ = v___x_4028_;
goto v___jp_4018_;
}
}
v___jp_4029_:
{
lean_object* v_fst_4031_; uint8_t v___x_4032_; 
v_fst_4031_ = lean_ctor_get(v___y_4030_, 0);
v___x_4032_ = lean_unbox(v_fst_4031_);
if (v___x_4032_ == 0)
{
lean_object* v_snd_4033_; 
v_snd_4033_ = lean_ctor_get(v___y_4030_, 1);
lean_inc(v_snd_4033_);
lean_dec_ref(v___y_4030_);
v_snd_4024_ = v_snd_4033_;
goto v___jp_4023_;
}
else
{
lean_object* v_snd_4034_; uint8_t v___x_4035_; 
lean_inc(v_fst_4031_);
lean_dec_ref(v___f_3963_);
v_snd_4034_ = lean_ctor_get(v___y_4030_, 1);
lean_inc(v_snd_4034_);
lean_dec_ref(v___y_4030_);
v___x_4035_ = lean_unbox(v_fst_4031_);
lean_dec(v_fst_4031_);
v_fst_4001_ = v___x_4035_;
v_snd_4002_ = v_snd_4034_;
goto v___jp_4000_;
}
}
}
else
{
lean_object* v_type_4043_; lean_object* v___x_4044_; uint8_t v_fst_4046_; lean_object* v_mctx_4047_; lean_object* v___y_4063_; lean_object* v_mctx_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
v_type_4043_ = lean_ctor_get(v_val_3957_, 3);
v___x_4044_ = lean_st_ref_get(v___y_3937_);
v_mctx_4068_ = lean_ctor_get(v___x_4044_, 0);
lean_inc_ref_n(v_mctx_4068_, 2);
lean_dec(v___x_4044_);
v___x_4069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
lean_ctor_set(v___x_4070_, 1, v_mctx_4068_);
v___x_4071_ = l_Lean_Expr_hasFVar(v_type_4043_);
if (v___x_4071_ == 0)
{
uint8_t v___x_4072_; 
v___x_4072_ = l_Lean_Expr_hasMVar(v_type_4043_);
if (v___x_4072_ == 0)
{
lean_dec_ref_known(v___x_4070_, 2);
lean_dec_ref(v___f_3963_);
v_fst_4046_ = v___x_4072_;
v_mctx_4047_ = v_mctx_4068_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4073_; 
lean_dec_ref(v_mctx_4068_);
lean_inc_ref(v_type_4043_);
v___x_4073_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_4043_, v___x_4070_);
v___y_4063_ = v___x_4073_;
goto v___jp_4062_;
}
}
else
{
lean_object* v___x_4074_; 
lean_dec_ref(v_mctx_4068_);
lean_inc_ref(v_type_4043_);
v___x_4074_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3963_, v___f_3962_, v_type_4043_, v___x_4070_);
v___y_4063_ = v___x_4074_;
goto v___jp_4062_;
}
v___jp_4045_:
{
lean_object* v___x_4048_; lean_object* v_cache_4049_; lean_object* v_zetaDeltaFVarIds_4050_; lean_object* v_postponed_4051_; lean_object* v_diag_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4060_; 
v___x_4048_ = lean_st_ref_take(v___y_3937_);
v_cache_4049_ = lean_ctor_get(v___x_4048_, 1);
v_zetaDeltaFVarIds_4050_ = lean_ctor_get(v___x_4048_, 2);
v_postponed_4051_ = lean_ctor_get(v___x_4048_, 3);
v_diag_4052_ = lean_ctor_get(v___x_4048_, 4);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4048_, 0);
lean_dec(v_unused_4061_);
v___x_4054_ = v___x_4048_;
v_isShared_4055_ = v_isSharedCheck_4060_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_diag_4052_);
lean_inc(v_postponed_4051_);
lean_inc(v_zetaDeltaFVarIds_4050_);
lean_inc(v_cache_4049_);
lean_dec(v___x_4048_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4060_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v_mctx_4047_);
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_mctx_4047_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_cache_4049_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_zetaDeltaFVarIds_4050_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_postponed_4051_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_diag_4052_);
v___x_4057_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_st_ref_put(v___y_3937_, v___x_4057_);
v_a_3959_ = v_fst_4046_;
goto v___jp_3958_;
}
}
}
v___jp_4062_:
{
lean_object* v_snd_4064_; lean_object* v_fst_4065_; lean_object* v_mctx_4066_; uint8_t v___x_4067_; 
v_snd_4064_ = lean_ctor_get(v___y_4063_, 1);
lean_inc(v_snd_4064_);
v_fst_4065_ = lean_ctor_get(v___y_4063_, 0);
lean_inc(v_fst_4065_);
lean_dec_ref(v___y_4063_);
v_mctx_4066_ = lean_ctor_get(v_snd_4064_, 1);
lean_inc_ref(v_mctx_4066_);
lean_dec(v_snd_4064_);
v___x_4067_ = lean_unbox(v_fst_4065_);
lean_dec(v_fst_4065_);
v_fst_4046_ = v___x_4067_;
v_mctx_4047_ = v_mctx_4066_;
goto v___jp_4045_;
}
}
}
v___jp_3958_:
{
if (v_a_3959_ == 0)
{
v_a_3949_ = v_snd_3943_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = l_Lean_LocalDecl_fvarId(v_val_3957_);
v___x_3961_ = lean_array_push(v_snd_3943_, v___x_3960_);
v_a_3949_ = v___x_3961_;
goto v___jp_3948_;
}
}
}
v___jp_3948_:
{
lean_object* v___x_3951_; 
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 1, v_a_3949_);
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3951_ = v___x_3945_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_a_3949_);
v___x_3951_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
size_t v___x_3952_; size_t v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = ((size_t)1ULL);
v___x_3953_ = lean_usize_add(v_i_3934_, v___x_3952_);
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3932_, v_sz_3933_, v___x_3953_, v___x_3951_, v___y_3937_);
return v___x_3954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4077_, lean_object* v_sz_4078_, lean_object* v_i_4079_, lean_object* v_b_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
size_t v_sz_boxed_4086_; size_t v_i_boxed_4087_; lean_object* v_res_4088_; 
v_sz_boxed_4086_ = lean_unbox_usize(v_sz_4078_);
lean_dec(v_sz_4078_);
v_i_boxed_4087_ = lean_unbox_usize(v_i_4079_);
lean_dec(v_i_4079_);
v_res_4088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4077_, v_sz_boxed_4086_, v_i_boxed_4087_, v_b_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec_ref(v_as_4077_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4089_, lean_object* v_init_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_root_4096_; lean_object* v_tail_4097_; lean_object* v___x_4098_; 
v_root_4096_ = lean_ctor_get(v_t_4089_, 0);
v_tail_4097_ = lean_ctor_get(v_t_4089_, 1);
lean_inc_ref(v_init_4090_);
v___x_4098_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4090_, v_root_4096_, v_init_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec_ref(v_init_4090_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4135_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4135_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4135_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
if (lean_obj_tag(v_a_4099_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; 
v_a_4103_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v_a_4099_, 1);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v_a_4103_);
v___x_4105_ = v___x_4101_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; size_t v_sz_4110_; size_t v___x_4111_; lean_object* v___x_4112_; 
lean_del_object(v___x_4101_);
v_a_4107_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v_a_4099_, 1);
v___x_4108_ = lean_box(0);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v_a_4107_);
v_sz_4110_ = lean_array_size(v_tail_4097_);
v___x_4111_ = ((size_t)0ULL);
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4097_, v_sz_4110_, v___x_4111_, v___x_4109_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4126_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4126_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4126_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v_fst_4117_; 
v_fst_4117_ = lean_ctor_get(v_a_4113_, 0);
if (lean_obj_tag(v_fst_4117_) == 0)
{
lean_object* v_snd_4118_; lean_object* v___x_4120_; 
v_snd_4118_ = lean_ctor_get(v_a_4113_, 1);
lean_inc(v_snd_4118_);
lean_dec(v_a_4113_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v_snd_4118_);
v___x_4120_ = v___x_4115_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_snd_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
else
{
lean_object* v_val_4122_; lean_object* v___x_4124_; 
lean_inc_ref(v_fst_4117_);
lean_dec(v_a_4113_);
v_val_4122_ = lean_ctor_get(v_fst_4117_, 0);
lean_inc(v_val_4122_);
lean_dec_ref_known(v_fst_4117_, 1);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v_val_4122_);
v___x_4124_ = v___x_4115_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_val_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
v_a_4127_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4112_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4112_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4098_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4098_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4144_, lean_object* v_init_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4144_, v_init_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec_ref(v_t_4144_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4152_, lean_object* v_fvarIds_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4159_; 
lean_inc(v_goal_4152_);
v___x_4159_ = l_Lean_MVarId_getDecl(v_goal_4152_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v_lctx_4161_; lean_object* v_decls_4162_; lean_object* v___x_4163_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v_lctx_4161_ = lean_ctor_get(v_a_4160_, 1);
lean_inc_ref(v_lctx_4161_);
lean_dec(v_a_4160_);
v_decls_4162_ = lean_ctor_get(v_lctx_4161_, 1);
lean_inc_ref(v_decls_4162_);
lean_dec_ref(v_lctx_4161_);
v___x_4163_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4162_, v_fvarIds_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec_ref(v_decls_4162_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
v___x_4165_ = l_Lean_MVarId_tryClearMany(v_goal_4152_, v_a_4164_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_a_4164_);
return v___x_4165_;
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_goal_4152_);
v_a_4166_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4163_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4163_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_dec_ref(v_fvarIds_4153_);
lean_dec(v_goal_4152_);
v_a_4174_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4159_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4159_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4182_, lean_object* v_fvarIds_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4182_, v_fvarIds_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4190_, size_t v_sz_4191_, size_t v_i_4192_, lean_object* v_b_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4190_, v_sz_4191_, v_i_4192_, v_b_4193_, v___y_4195_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4200_, lean_object* v_sz_4201_, lean_object* v_i_4202_, lean_object* v_b_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
size_t v_sz_boxed_4209_; size_t v_i_boxed_4210_; lean_object* v_res_4211_; 
v_sz_boxed_4209_ = lean_unbox_usize(v_sz_4201_);
lean_dec(v_sz_4201_);
v_i_boxed_4210_ = lean_unbox_usize(v_i_4202_);
lean_dec(v_i_4202_);
v_res_4211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4200_, v_sz_boxed_4209_, v_i_boxed_4210_, v_b_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_as_4200_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4212_, size_t v_sz_4213_, size_t v_i_4214_, lean_object* v_b_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4212_, v_sz_4213_, v_i_4214_, v_b_4215_, v___y_4217_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4222_, lean_object* v_sz_4223_, lean_object* v_i_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4223_);
lean_dec(v_sz_4223_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4224_);
lean_dec(v_i_4224_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4222_, v_sz_boxed_4231_, v_i_boxed_4232_, v_b_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_as_4222_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4234_, lean_object* v_as_4235_, size_t v_sz_4236_, size_t v_i_4237_, lean_object* v_b_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_usize_dec_lt(v_i_4237_, v_sz_4236_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v_b_4238_);
return v___x_4247_;
}
else
{
lean_object* v_a_4248_; lean_object* v_fst_4249_; lean_object* v_snd_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_a_4248_ = lean_array_uget_borrowed(v_as_4235_, v_i_4237_);
v_fst_4249_ = lean_ctor_get(v_a_4248_, 0);
v_snd_4250_ = lean_ctor_get(v_a_4248_, 1);
v___x_4251_ = lean_box(0);
lean_inc(v_snd_4250_);
v___x_4252_ = l_Lean_Meta_FVarSubst_get(v_fs_4234_, v_snd_4250_);
lean_inc(v_fst_4249_);
v___x_4253_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4249_, v___x_4252_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4253_) == 0)
{
size_t v___x_4254_; size_t v___x_4255_; 
lean_dec_ref_known(v___x_4253_, 1);
v___x_4254_ = ((size_t)1ULL);
v___x_4255_ = lean_usize_add(v_i_4237_, v___x_4254_);
v_i_4237_ = v___x_4255_;
v_b_4238_ = v___x_4251_;
goto _start;
}
else
{
return v___x_4253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4257_, lean_object* v_as_4258_, lean_object* v_sz_4259_, lean_object* v_i_4260_, lean_object* v_b_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
size_t v_sz_boxed_4269_; size_t v_i_boxed_4270_; lean_object* v_res_4271_; 
v_sz_boxed_4269_ = lean_unbox_usize(v_sz_4259_);
lean_dec(v_sz_4259_);
v_i_boxed_4270_ = lean_unbox_usize(v_i_4260_);
lean_dec(v_i_4260_);
v_res_4271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4257_, v_as_4258_, v_sz_boxed_4269_, v_i_boxed_4270_, v_b_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v_as_4258_);
lean_dec(v_fs_4257_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4272_, lean_object* v_toTag_4273_, size_t v_sz_4274_, size_t v___x_4275_, lean_object* v___x_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4272_, v_toTag_4273_, v_sz_4274_, v___x_4275_, v___x_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4291_ == 0)
{
lean_object* v_unused_4292_; 
v_unused_4292_ = lean_ctor_get(v___x_4284_, 0);
lean_dec(v_unused_4292_);
v___x_4286_ = v___x_4284_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_dec(v___x_4284_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v___x_4276_);
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4276_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
else
{
return v___x_4284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4293_, lean_object* v_toTag_4294_, lean_object* v_sz_4295_, lean_object* v___x_4296_, lean_object* v___x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
size_t v_sz_boxed_4305_; size_t v___x_1634__boxed_4306_; lean_object* v_res_4307_; 
v_sz_boxed_4305_ = lean_unbox_usize(v_sz_4295_);
lean_dec(v_sz_4295_);
v___x_1634__boxed_4306_ = lean_unbox_usize(v___x_4296_);
lean_dec(v___x_4296_);
v_res_4307_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4293_, v_toTag_4294_, v_sz_boxed_4305_, v___x_1634__boxed_4306_, v___x_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v_toTag_4294_);
lean_dec(v_fs_4293_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4308_, size_t v_i_4309_, size_t v_stop_4310_, lean_object* v_b_4311_){
_start:
{
lean_object* v___y_4313_; uint8_t v___x_4317_; 
v___x_4317_ = lean_usize_dec_eq(v_i_4309_, v_stop_4310_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = lean_array_uget_borrowed(v_as_4308_, v_i_4309_);
v___x_4319_ = l_Lean_Expr_isFVar(v___x_4318_);
if (v___x_4319_ == 0)
{
v___y_4313_ = v_b_4311_;
goto v___jp_4312_;
}
else
{
lean_object* v___x_4320_; 
lean_inc(v___x_4318_);
v___x_4320_ = lean_array_push(v_b_4311_, v___x_4318_);
v___y_4313_ = v___x_4320_;
goto v___jp_4312_;
}
}
else
{
return v_b_4311_;
}
v___jp_4312_:
{
size_t v___x_4314_; size_t v___x_4315_; 
v___x_4314_ = ((size_t)1ULL);
v___x_4315_ = lean_usize_add(v_i_4309_, v___x_4314_);
v_i_4309_ = v___x_4315_;
v_b_4311_ = v___y_4313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4321_, lean_object* v_i_4322_, lean_object* v_stop_4323_, lean_object* v_b_4324_){
_start:
{
size_t v_i_boxed_4325_; size_t v_stop_boxed_4326_; lean_object* v_res_4327_; 
v_i_boxed_4325_ = lean_unbox_usize(v_i_4322_);
lean_dec(v_i_4322_);
v_stop_boxed_4326_ = lean_unbox_usize(v_stop_4323_);
lean_dec(v_stop_4323_);
v_res_4327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4321_, v_i_boxed_4325_, v_stop_boxed_4326_, v_b_4324_);
lean_dec_ref(v_as_4321_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4328_, size_t v_sz_4329_, size_t v_i_4330_, lean_object* v_bs_4331_){
_start:
{
uint8_t v___x_4332_; 
v___x_4332_ = lean_usize_dec_lt(v_i_4330_, v_sz_4329_);
if (v___x_4332_ == 0)
{
return v_bs_4331_;
}
else
{
lean_object* v_v_4333_; lean_object* v___x_4334_; lean_object* v_bs_x27_4335_; lean_object* v___x_4336_; size_t v___x_4337_; size_t v___x_4338_; lean_object* v___x_4339_; 
v_v_4333_ = lean_array_uget(v_bs_4331_, v_i_4330_);
v___x_4334_ = lean_unsigned_to_nat(0u);
v_bs_x27_4335_ = lean_array_uset(v_bs_4331_, v_i_4330_, v___x_4334_);
v___x_4336_ = l_Lean_Meta_FVarSubst_get(v_fs_4328_, v_v_4333_);
v___x_4337_ = ((size_t)1ULL);
v___x_4338_ = lean_usize_add(v_i_4330_, v___x_4337_);
v___x_4339_ = lean_array_uset(v_bs_x27_4335_, v_i_4330_, v___x_4336_);
v_i_4330_ = v___x_4338_;
v_bs_4331_ = v___x_4339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4341_, lean_object* v_sz_4342_, lean_object* v_i_4343_, lean_object* v_bs_4344_){
_start:
{
size_t v_sz_boxed_4345_; size_t v_i_boxed_4346_; lean_object* v_res_4347_; 
v_sz_boxed_4345_ = lean_unbox_usize(v_sz_4342_);
lean_dec(v_sz_4342_);
v_i_boxed_4346_ = lean_unbox_usize(v_i_4343_);
lean_dec(v_i_4343_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4341_, v_sz_boxed_4345_, v_i_boxed_4346_, v_bs_4344_);
lean_dec(v_fs_4341_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4348_, size_t v_i_4349_, lean_object* v_bs_4350_){
_start:
{
uint8_t v___x_4351_; 
v___x_4351_ = lean_usize_dec_lt(v_i_4349_, v_sz_4348_);
if (v___x_4351_ == 0)
{
return v_bs_4350_;
}
else
{
lean_object* v_v_4352_; lean_object* v___x_4353_; lean_object* v_bs_x27_4354_; lean_object* v___x_4355_; size_t v___x_4356_; size_t v___x_4357_; lean_object* v___x_4358_; 
v_v_4352_ = lean_array_uget(v_bs_4350_, v_i_4349_);
v___x_4353_ = lean_unsigned_to_nat(0u);
v_bs_x27_4354_ = lean_array_uset(v_bs_4350_, v_i_4349_, v___x_4353_);
v___x_4355_ = l_Lean_Expr_fvarId_x21(v_v_4352_);
lean_dec(v_v_4352_);
v___x_4356_ = ((size_t)1ULL);
v___x_4357_ = lean_usize_add(v_i_4349_, v___x_4356_);
v___x_4358_ = lean_array_uset(v_bs_x27_4354_, v_i_4349_, v___x_4355_);
v_i_4349_ = v___x_4357_;
v_bs_4350_ = v___x_4358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4360_, lean_object* v_i_4361_, lean_object* v_bs_4362_){
_start:
{
size_t v_sz_boxed_4363_; size_t v_i_boxed_4364_; lean_object* v_res_4365_; 
v_sz_boxed_4363_ = lean_unbox_usize(v_sz_4360_);
lean_dec(v_sz_4360_);
v_i_boxed_4364_ = lean_unbox_usize(v_i_4361_);
lean_dec(v_i_4361_);
v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4363_, v_i_boxed_4364_, v_bs_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4370_, lean_object* v_g_4371_, lean_object* v_fs_4372_, lean_object* v_clears_4373_, lean_object* v_gs_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v___y_4383_; size_t v_sz_4420_; size_t v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; uint8_t v___x_4426_; 
v_sz_4420_ = lean_array_size(v_clears_4373_);
v___x_4421_ = ((size_t)0ULL);
v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4372_, v_sz_4420_, v___x_4421_, v_clears_4373_);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_array_get_size(v___x_4422_);
v___x_4425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4426_ = lean_nat_dec_lt(v___x_4423_, v___x_4424_);
if (v___x_4426_ == 0)
{
lean_dec_ref(v___x_4422_);
v___y_4383_ = v___x_4425_;
goto v___jp_4382_;
}
else
{
size_t v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_usize_of_nat(v___x_4424_);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4422_, v___x_4421_, v___x_4427_, v___x_4425_);
lean_dec_ref(v___x_4422_);
v___y_4383_ = v___x_4428_;
goto v___jp_4382_;
}
v___jp_4382_:
{
size_t v_sz_4384_; size_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_sz_4384_ = lean_array_size(v___y_4383_);
v___x_4385_ = ((size_t)0ULL);
v___x_4386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4384_, v___x_4385_, v___y_4383_);
v___x_4387_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4371_, v___x_4386_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4389_; size_t v_sz_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___f_4393_; lean_object* v___x_4394_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc_n(v_a_4388_, 2);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4389_ = lean_box(0);
v_sz_4390_ = lean_array_size(v_toTag_4370_);
v___x_4391_ = lean_box_usize(v_sz_4390_);
v___x_4392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4393_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4393_, 0, v_fs_4372_);
lean_closure_set(v___f_4393_, 1, v_toTag_4370_);
lean_closure_set(v___f_4393_, 2, v___x_4391_);
lean_closure_set(v___f_4393_, 3, v___x_4392_);
lean_closure_set(v___f_4393_, 4, v___x_4389_);
v___x_4394_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4388_, v___f_4393_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4402_; 
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v___x_4394_, 0);
lean_dec(v_unused_4403_);
v___x_4396_ = v___x_4394_;
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
else
{
lean_dec(v___x_4394_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = lean_array_push(v_gs_4374_, v_a_4388_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4398_);
v___x_4400_ = v___x_4396_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_a_4388_);
lean_dec_ref(v_gs_4374_);
v_a_4404_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4394_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4394_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref(v_gs_4374_);
lean_dec(v_fs_4372_);
lean_dec_ref(v_toTag_4370_);
v_a_4412_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4387_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4387_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4429_, lean_object* v_g_4430_, lean_object* v_fs_4431_, lean_object* v_clears_4432_, lean_object* v_gs_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4429_, v_g_4430_, v_fs_4431_, v_clears_4432_, v_gs_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
lean_dec(v_a_4439_);
lean_dec_ref(v_a_4438_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
return v_res_4441_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = lean_box(0);
v___x_4443_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
lean_ctor_set(v___x_4444_, 1, v___x_4442_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4508_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4502_);
v___x_4509_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4502_);
v___x_4511_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4502_);
v___x_4513_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4502_);
v___x_4515_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4502_);
v___x_4517_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4502_);
v___x_4519_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4502_);
v___x_4521_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4502_);
v___x_4523_ = l_Lean_Syntax_isOfKind(v_stx_4502_, v___x_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
lean_dec(v_stx_4502_);
v___x_4524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4524_;
}
else
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4525_);
v___x_4527_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4526_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4536_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4534_; 
v___x_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4532_, 0, v_stx_4502_);
lean_ctor_set(v___x_4532_, 1, v_a_4528_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4532_);
v___x_4534_ = v___x_4530_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
else
{
lean_dec(v_stx_4502_);
return v___x_4527_;
}
}
}
else
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v_ps_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4537_ = lean_unsigned_to_nat(1u);
v___x_4538_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4537_);
v_ps_4539_ = l_Lean_Syntax_getArgs(v___x_4538_);
lean_dec(v___x_4538_);
v___x_4540_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4539_);
lean_dec_ref(v_ps_4539_);
v___x_4541_ = lean_array_to_list(v___x_4540_);
v___x_4542_ = lean_box(0);
v___x_4543_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4541_, v___x_4542_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4552_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4552_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4548_, 0, v_stx_4502_);
lean_ctor_set(v___x_4548_, 1, v_a_4544_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4550_ = v___x_4546_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v_stx_4502_);
v_a_4553_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4543_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4543_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4561_);
v___x_4563_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4562_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4572_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4566_ = v___x_4563_;
v_isShared_4567_ = v_isSharedCheck_4572_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4572_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; lean_object* v___x_4570_; 
v___x_4568_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4568_, 0, v_stx_4502_);
lean_ctor_set(v___x_4568_, 1, v_a_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4568_);
v___x_4570_ = v___x_4566_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
else
{
lean_dec(v_stx_4502_);
return v___x_4563_;
}
}
}
else
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4573_, 0, v_stx_4502_);
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
return v___x_4574_;
}
}
else
{
lean_object* v___x_4575_; lean_object* v_h_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4575_ = lean_unsigned_to_nat(0u);
v_h_4576_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4575_);
lean_dec(v_stx_4502_);
v___x_4577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4576_);
v___x_4578_ = l_Lean_Syntax_isOfKind(v_h_4576_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
lean_dec(v_h_4576_);
v___x_4579_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4579_;
}
else
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = l_Lean_TSyntax_getId(v_h_4576_);
v___x_4581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4581_, 0, v_h_4576_);
lean_ctor_set(v___x_4581_, 1, v___x_4580_);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
return v___x_4582_;
}
}
}
else
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4584_, 0, v_stx_4502_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; 
v___x_4586_ = lean_unsigned_to_nat(0u);
v___x_4587_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4586_);
lean_inc(v___x_4587_);
v___x_4588_ = l_Lean_Syntax_isOfKind(v___x_4587_, v___x_4508_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
lean_dec(v___x_4587_);
lean_dec(v_stx_4502_);
v___x_4589_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4589_;
}
else
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4590_ = lean_unsigned_to_nat(1u);
v___x_4591_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4590_);
v___x_4592_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4591_);
v___x_4593_ = l_Lean_Syntax_matchesNull(v___x_4591_, v___x_4592_);
if (v___x_4593_ == 0)
{
uint8_t v___x_4594_; 
lean_dec(v_stx_4502_);
v___x_4594_ = l_Lean_Syntax_matchesNull(v___x_4591_, v___x_4586_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; 
lean_dec(v___x_4587_);
v___x_4595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4595_;
}
else
{
v_stx_4502_ = v___x_4587_;
goto _start;
}
}
else
{
lean_object* v_t_4597_; lean_object* v___x_4598_; 
v_t_4597_ = l_Lean_Syntax_getArg(v___x_4591_, v___x_4590_);
lean_dec(v___x_4591_);
v___x_4598_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4587_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4607_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4607_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4603_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4603_, 0, v_stx_4502_);
lean_ctor_set(v___x_4603_, 1, v_a_4599_);
lean_ctor_set(v___x_4603_, 2, v_t_4597_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4603_);
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_dec(v_t_4597_);
lean_dec(v_stx_4502_);
return v___x_4598_;
}
}
}
}
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v_ps_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = l_Lean_Syntax_getArg(v_stx_4502_, v___x_4608_);
v_ps_4610_ = l_Lean_Syntax_getArgs(v___x_4609_);
lean_dec(v___x_4609_);
v___x_4611_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4610_);
lean_dec_ref(v_ps_4610_);
v___x_4612_ = lean_array_to_list(v___x_4611_);
v___x_4613_ = lean_box(0);
v___x_4614_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4612_, v___x_4613_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4623_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4623_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4502_, v_a_4615_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_stx_4502_);
v_a_4624_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4614_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4614_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4632_, lean_object* v_x_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
if (lean_obj_tag(v_x_4632_) == 0)
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = l_List_reverse___redArg(v_x_4633_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
else
{
lean_object* v_head_4641_; lean_object* v_tail_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4660_; 
v_head_4641_ = lean_ctor_get(v_x_4632_, 0);
v_tail_4642_ = lean_ctor_get(v_x_4632_, 1);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_x_4632_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4644_ = v_x_4632_;
v_isShared_4645_ = v_isSharedCheck_4660_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_tail_4642_);
lean_inc(v_head_4641_);
lean_dec(v_x_4632_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4660_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; 
v___x_4646_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4641_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 1, v_x_4633_);
lean_ctor_set(v___x_4644_, 0, v_a_4647_);
v___x_4649_ = v___x_4644_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4647_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_x_4633_);
v___x_4649_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
v_x_4632_ = v_tail_4642_;
v_x_4633_ = v___x_4649_;
goto _start;
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_del_object(v___x_4644_);
lean_dec(v_tail_4642_);
lean_dec(v_x_4633_);
v_a_4652_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4646_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4646_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4661_, lean_object* v_x_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4661_, v_x_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4676_, lean_object* v_as_4677_, size_t v_sz_4678_, size_t v_i_4679_, lean_object* v_b_4680_){
_start:
{
lean_object* v_a_4683_; uint8_t v___x_4687_; 
v___x_4687_ = lean_usize_dec_lt(v_i_4679_, v_sz_4678_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_b_4680_);
return v___x_4688_;
}
else
{
lean_object* v_fst_4689_; lean_object* v_snd_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4710_; 
v_fst_4689_ = lean_ctor_get(v_b_4680_, 0);
v_snd_4690_ = lean_ctor_get(v_b_4680_, 1);
v_isSharedCheck_4710_ = !lean_is_exclusive(v_b_4680_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4692_ = v_b_4680_;
v_isShared_4693_ = v_isSharedCheck_4710_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_snd_4690_);
lean_inc(v_fst_4689_);
lean_dec(v_b_4680_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4710_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v_a_4694_; lean_object* v_expr_4695_; lean_object* v_hName_x3f_4696_; lean_object* v___x_4697_; uint8_t v___x_4707_; 
v_a_4694_ = lean_array_uget_borrowed(v_as_4677_, v_i_4679_);
v_expr_4695_ = lean_ctor_get(v_a_4694_, 0);
v_hName_x3f_4696_ = lean_ctor_get(v_a_4694_, 2);
v___x_4697_ = lean_box(0);
v___x_4707_ = l_Lean_Expr_isFVar(v_expr_4695_);
if (v___x_4707_ == 0)
{
goto v___jp_4698_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4696_) == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_del_object(v___x_4692_);
lean_inc_ref(v_expr_4695_);
v___x_4708_ = lean_array_push(v_fst_4689_, v_expr_4695_);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
lean_ctor_set(v___x_4709_, 1, v_snd_4690_);
v_a_4683_ = v___x_4709_;
goto v___jp_4682_;
}
else
{
goto v___jp_4698_;
}
}
v___jp_4698_:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4699_ = lean_array_get_borrowed(v___x_4697_, v_fst_4676_, v_snd_4690_);
lean_inc(v___x_4699_);
v___x_4700_ = l_Lean_mkFVar(v___x_4699_);
v___x_4701_ = lean_array_push(v_fst_4689_, v___x_4700_);
v___x_4702_ = lean_unsigned_to_nat(1u);
v___x_4703_ = lean_nat_add(v_snd_4690_, v___x_4702_);
lean_dec(v_snd_4690_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 1, v___x_4703_);
lean_ctor_set(v___x_4692_, 0, v___x_4701_);
v___x_4705_ = v___x_4692_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4703_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
v_a_4683_ = v___x_4705_;
goto v___jp_4682_;
}
}
}
}
v___jp_4682_:
{
size_t v___x_4684_; size_t v___x_4685_; 
v___x_4684_ = ((size_t)1ULL);
v___x_4685_ = lean_usize_add(v_i_4679_, v___x_4684_);
v_i_4679_ = v___x_4685_;
v_b_4680_ = v_a_4683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4711_, lean_object* v_as_4712_, lean_object* v_sz_4713_, lean_object* v_i_4714_, lean_object* v_b_4715_, lean_object* v___y_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4713_);
lean_dec(v_sz_4713_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4711_, v_as_4712_, v_sz_boxed_4717_, v_i_boxed_4718_, v_b_4715_);
lean_dec_ref(v_as_4712_);
lean_dec_ref(v_fst_4711_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4720_, size_t v_i_4721_, size_t v_stop_4722_, lean_object* v_b_4723_){
_start:
{
lean_object* v___y_4725_; uint8_t v___x_4729_; 
v___x_4729_ = lean_usize_dec_eq(v_i_4721_, v_stop_4722_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v_expr_4731_; lean_object* v_hName_x3f_4732_; uint8_t v___x_4733_; 
v___x_4730_ = lean_array_uget_borrowed(v_as_4720_, v_i_4721_);
v_expr_4731_ = lean_ctor_get(v___x_4730_, 0);
v_hName_x3f_4732_ = lean_ctor_get(v___x_4730_, 2);
v___x_4733_ = l_Lean_Expr_isFVar(v_expr_4731_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; 
lean_inc(v___x_4730_);
v___x_4734_ = lean_array_push(v_b_4723_, v___x_4730_);
v___y_4725_ = v___x_4734_;
goto v___jp_4724_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4732_) == 0)
{
v___y_4725_ = v_b_4723_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4735_; 
lean_inc(v___x_4730_);
v___x_4735_ = lean_array_push(v_b_4723_, v___x_4730_);
v___y_4725_ = v___x_4735_;
goto v___jp_4724_;
}
}
}
else
{
return v_b_4723_;
}
v___jp_4724_:
{
size_t v___x_4726_; size_t v___x_4727_; 
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4721_, v___x_4726_);
v_i_4721_ = v___x_4727_;
v_b_4723_ = v___y_4725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4736_, lean_object* v_i_4737_, lean_object* v_stop_4738_, lean_object* v_b_4739_){
_start:
{
size_t v_i_boxed_4740_; size_t v_stop_boxed_4741_; lean_object* v_res_4742_; 
v_i_boxed_4740_ = lean_unbox_usize(v_i_4737_);
lean_dec(v_i_4737_);
v_stop_boxed_4741_ = lean_unbox_usize(v_stop_4738_);
lean_dec(v_stop_4738_);
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4736_, v_i_boxed_4740_, v_stop_boxed_4741_, v_b_4739_);
lean_dec_ref(v_as_4736_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4748_, lean_object* v_args_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v_lower_4759_; lean_object* v_upper_4760_; lean_object* v_j_4766_; lean_object* v___y_4768_; lean_object* v___x_4799_; lean_object* v___x_4800_; uint8_t v___x_4801_; 
v_j_4766_ = lean_unsigned_to_nat(0u);
v___x_4799_ = lean_array_get_size(v_args_4749_);
v___x_4800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4801_ = lean_nat_dec_lt(v_j_4766_, v___x_4799_);
if (v___x_4801_ == 0)
{
v___y_4768_ = v___x_4800_;
goto v___jp_4767_;
}
else
{
size_t v___x_4802_; size_t v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = ((size_t)0ULL);
v___x_4803_ = lean_usize_of_nat(v___x_4799_);
v___x_4804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4749_, v___x_4802_, v___x_4803_, v___x_4800_);
v___y_4768_ = v___x_4804_;
goto v___jp_4767_;
}
v___jp_4755_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4761_ = l_Array_toSubarray___redArg(v___y_4758_, v_lower_4759_, v_upper_4760_);
v___x_4762_ = l_Subarray_copy___redArg(v___x_4761_);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
lean_ctor_set(v___x_4763_, 1, v___y_4757_);
v___x_4764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4764_, 0, v___y_4756_);
lean_ctor_set(v___x_4764_, 1, v___x_4763_);
v___x_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
return v___x_4765_;
}
v___jp_4767_:
{
uint8_t v___x_4769_; lean_object* v___x_4770_; 
v___x_4769_ = 3;
v___x_4770_ = l_Lean_MVarId_generalize(v_goal_4748_, v___y_4768_, v___x_4769_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v_fst_4772_; lean_object* v_snd_4773_; lean_object* v___x_4774_; size_t v_sz_4775_; size_t v___x_4776_; lean_object* v___x_4777_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4770_, 1);
v_fst_4772_ = lean_ctor_get(v_a_4771_, 0);
lean_inc(v_fst_4772_);
v_snd_4773_ = lean_ctor_get(v_a_4771_, 1);
lean_inc(v_snd_4773_);
lean_dec(v_a_4771_);
v___x_4774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4775_ = lean_array_size(v_args_4749_);
v___x_4776_ = ((size_t)0ULL);
v___x_4777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4772_, v_args_4749_, v_sz_4775_, v___x_4776_, v___x_4774_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v_fst_4779_; lean_object* v_snd_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v___x_4777_, 1);
v_fst_4779_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_fst_4779_);
v_snd_4780_ = lean_ctor_get(v_a_4778_, 1);
lean_inc(v_snd_4780_);
lean_dec(v_a_4778_);
v___x_4781_ = lean_array_get_size(v_fst_4772_);
v___x_4782_ = lean_nat_dec_le(v_snd_4780_, v_j_4766_);
if (v___x_4782_ == 0)
{
v___y_4756_ = v_fst_4779_;
v___y_4757_ = v_snd_4773_;
v___y_4758_ = v_fst_4772_;
v_lower_4759_ = v_snd_4780_;
v_upper_4760_ = v___x_4781_;
goto v___jp_4755_;
}
else
{
lean_dec(v_snd_4780_);
v___y_4756_ = v_fst_4779_;
v___y_4757_ = v_snd_4773_;
v___y_4758_ = v_fst_4772_;
v_lower_4759_ = v_j_4766_;
v_upper_4760_ = v___x_4781_;
goto v___jp_4755_;
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v_snd_4773_);
lean_dec(v_fst_4772_);
v_a_4783_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4777_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4777_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
v_a_4791_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4770_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4770_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4805_, lean_object* v_args_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4805_, v_args_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec_ref(v_args_4806_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4813_, lean_object* v_as_4814_, size_t v_sz_4815_, size_t v_i_4816_, lean_object* v_b_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4813_, v_as_4814_, v_sz_4815_, v_i_4816_, v_b_4817_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4824_, lean_object* v_as_4825_, lean_object* v_sz_4826_, lean_object* v_i_4827_, lean_object* v_b_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
size_t v_sz_boxed_4834_; size_t v_i_boxed_4835_; lean_object* v_res_4836_; 
v_sz_boxed_4834_ = lean_unbox_usize(v_sz_4826_);
lean_dec(v_sz_4826_);
v_i_boxed_4835_ = lean_unbox_usize(v_i_4827_);
lean_dec(v_i_4827_);
v_res_4836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4824_, v_as_4825_, v_sz_boxed_4834_, v_i_boxed_4835_, v_b_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec_ref(v_as_4825_);
lean_dec_ref(v_fst_4824_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4837_, size_t v_i_4838_, size_t v_stop_4839_, lean_object* v_b_4840_){
_start:
{
lean_object* v___y_4842_; uint8_t v___x_4846_; 
v___x_4846_ = lean_usize_dec_eq(v_i_4838_, v_stop_4839_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; lean_object* v_fst_4848_; 
v___x_4847_ = lean_array_uget_borrowed(v_as_4837_, v_i_4838_);
v_fst_4848_ = lean_ctor_get(v___x_4847_, 0);
if (lean_obj_tag(v_fst_4848_) == 0)
{
v___y_4842_ = v_b_4840_;
goto v___jp_4841_;
}
else
{
lean_object* v_val_4849_; lean_object* v___x_4850_; 
v_val_4849_ = lean_ctor_get(v_fst_4848_, 0);
lean_inc(v_val_4849_);
v___x_4850_ = lean_array_push(v_b_4840_, v_val_4849_);
v___y_4842_ = v___x_4850_;
goto v___jp_4841_;
}
}
else
{
return v_b_4840_;
}
v___jp_4841_:
{
size_t v___x_4843_; size_t v___x_4844_; 
v___x_4843_ = ((size_t)1ULL);
v___x_4844_ = lean_usize_add(v_i_4838_, v___x_4843_);
v_i_4838_ = v___x_4844_;
v_b_4840_ = v___y_4842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4851_, lean_object* v_i_4852_, lean_object* v_stop_4853_, lean_object* v_b_4854_){
_start:
{
size_t v_i_boxed_4855_; size_t v_stop_boxed_4856_; lean_object* v_res_4857_; 
v_i_boxed_4855_ = lean_unbox_usize(v_i_4852_);
lean_dec(v_i_4852_);
v_stop_boxed_4856_ = lean_unbox_usize(v_stop_4853_);
lean_dec(v_stop_4853_);
v_res_4857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4851_, v_i_boxed_4855_, v_stop_boxed_4856_, v_b_4854_);
lean_dec_ref(v_as_4851_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4860_, lean_object* v_start_4861_, lean_object* v_stop_4862_){
_start:
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4864_ = lean_nat_dec_lt(v_start_4861_, v_stop_4862_);
if (v___x_4864_ == 0)
{
return v___x_4863_;
}
else
{
lean_object* v___x_4865_; uint8_t v___x_4866_; 
v___x_4865_ = lean_array_get_size(v_as_4860_);
v___x_4866_ = lean_nat_dec_le(v_stop_4862_, v___x_4865_);
if (v___x_4866_ == 0)
{
uint8_t v___x_4867_; 
v___x_4867_ = lean_nat_dec_lt(v_start_4861_, v___x_4865_);
if (v___x_4867_ == 0)
{
return v___x_4863_;
}
else
{
size_t v___x_4868_; size_t v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = lean_usize_of_nat(v_start_4861_);
v___x_4869_ = lean_usize_of_nat(v___x_4865_);
v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4860_, v___x_4868_, v___x_4869_, v___x_4863_);
return v___x_4870_;
}
}
else
{
size_t v___x_4871_; size_t v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = lean_usize_of_nat(v_start_4861_);
v___x_4872_ = lean_usize_of_nat(v_stop_4862_);
v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4860_, v___x_4871_, v___x_4872_, v___x_4863_);
return v___x_4873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4874_, lean_object* v_start_4875_, lean_object* v_stop_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4874_, v_start_4875_, v_stop_4876_);
lean_dec(v_stop_4876_);
lean_dec(v_start_4875_);
lean_dec_ref(v_as_4874_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4878_, lean_object* v_bs_4879_, lean_object* v_i_4880_, lean_object* v_cs_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v___y_4890_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4900_ = lean_array_get_size(v_as_4878_);
v___x_4901_ = lean_nat_dec_lt(v_i_4880_, v___x_4900_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; 
lean_dec(v_i_4880_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v_cs_4881_);
return v___x_4902_;
}
else
{
lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4903_ = lean_array_get_size(v_bs_4879_);
v___x_4904_ = lean_nat_dec_lt(v_i_4880_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
lean_dec(v_i_4880_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v_cs_4881_);
return v___x_4905_;
}
else
{
lean_object* v_a_4906_; lean_object* v_fst_4907_; lean_object* v_snd_4908_; lean_object* v_fst_4910_; lean_object* v_snd_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v_b_4949_; 
v_a_4906_ = lean_array_fget_borrowed(v_as_4878_, v_i_4880_);
v_fst_4907_ = lean_ctor_get(v_a_4906_, 0);
lean_inc(v_fst_4907_);
v_snd_4908_ = lean_ctor_get(v_a_4906_, 1);
v_b_4949_ = lean_array_fget(v_bs_4879_, v_i_4880_);
if (lean_obj_tag(v_b_4949_) == 4)
{
lean_object* v_ref_4950_; lean_object* v_a_4951_; lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4989_; 
v_ref_4950_ = lean_ctor_get(v_b_4949_, 0);
v_a_4951_ = lean_ctor_get(v_b_4949_, 1);
v_a_4952_ = lean_ctor_get(v_b_4949_, 2);
v_isSharedCheck_4989_ = !lean_is_exclusive(v_b_4949_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4954_ = v_b_4949_;
v_isShared_4955_ = v_isSharedCheck_4989_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_inc(v_a_4951_);
lean_inc(v_ref_4950_);
lean_dec(v_b_4949_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4989_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v_toCold_4956_; lean_object* v_currRecDepth_4957_; lean_object* v_ref_4958_; uint16_t v_optionFlags_4959_; uint8_t v_suppressElabErrors_4960_; uint8_t v_checkDeprecated_4961_; uint8_t v_isRecordingDeps_4962_; lean_object* v_ref_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v_toCold_4956_ = lean_ctor_get(v___y_4886_, 0);
v_currRecDepth_4957_ = lean_ctor_get(v___y_4886_, 1);
v_ref_4958_ = lean_ctor_get(v___y_4886_, 2);
v_optionFlags_4959_ = lean_ctor_get_uint16(v___y_4886_, sizeof(void*)*3);
v_suppressElabErrors_4960_ = lean_ctor_get_uint8(v___y_4886_, sizeof(void*)*3 + 2);
v_checkDeprecated_4961_ = lean_ctor_get_uint8(v___y_4886_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4962_ = lean_ctor_get_uint8(v___y_4886_, sizeof(void*)*3 + 4);
v_ref_4963_ = l_Lean_replaceRef(v_ref_4950_, v_ref_4958_);
lean_inc(v_currRecDepth_4957_);
lean_inc_ref(v_toCold_4956_);
v___x_4964_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4964_, 0, v_toCold_4956_);
lean_ctor_set(v___x_4964_, 1, v_currRecDepth_4957_);
lean_ctor_set(v___x_4964_, 2, v_ref_4963_);
lean_ctor_set_uint16(v___x_4964_, sizeof(void*)*3, v_optionFlags_4959_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*3 + 2, v_suppressElabErrors_4960_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*3 + 3, v_checkDeprecated_4961_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*3 + 4, v_isRecordingDeps_4962_);
v___x_4965_ = l_Lean_Elab_Term_elabType(v_a_4952_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___x_4964_, v___y_4887_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4967_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc_n(v_a_4966_, 2);
lean_dec_ref_known(v___x_4965_, 1);
v___x_4967_ = l_Lean_Elab_Term_exprToSyntax(v_a_4966_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___x_4964_, v___y_4887_);
lean_dec_ref_known(v___x_4964_, 3);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref_known(v___x_4967_, 1);
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 2, v_a_4968_);
v___x_4970_ = v___x_4954_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_ref_4950_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v_a_4951_);
lean_ctor_set(v_reuseFailAlloc_4972_, 2, v_a_4968_);
v___x_4970_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; 
v___x_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4971_, 0, v_a_4966_);
v_fst_4910_ = v___x_4970_;
v_snd_4911_ = v___x_4971_;
v___y_4912_ = v___y_4882_;
v___y_4913_ = v___y_4883_;
v___y_4914_ = v___y_4884_;
v___y_4915_ = v___y_4885_;
v___y_4916_ = v___y_4886_;
v___y_4917_ = v___y_4887_;
goto v___jp_4909_;
}
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec(v_a_4966_);
lean_del_object(v___x_4954_);
lean_dec_ref(v_a_4951_);
lean_dec(v_ref_4950_);
lean_dec(v_fst_4907_);
lean_dec_ref(v_cs_4881_);
lean_dec(v_i_4880_);
v_a_4973_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4967_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4967_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref_known(v___x_4964_, 3);
lean_del_object(v___x_4954_);
lean_dec_ref(v_a_4951_);
lean_dec(v_ref_4950_);
lean_dec(v_fst_4907_);
lean_dec_ref(v_cs_4881_);
lean_dec(v_i_4880_);
v_a_4981_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4965_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4965_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
}
else
{
lean_object* v___x_4990_; 
v___x_4990_ = lean_box(0);
v_fst_4910_ = v_b_4949_;
v_snd_4911_ = v___x_4990_;
v___y_4912_ = v___y_4882_;
v___y_4913_ = v___y_4883_;
v___y_4914_ = v___y_4884_;
v___y_4915_ = v___y_4885_;
v___y_4916_ = v___y_4886_;
v___y_4917_ = v___y_4887_;
goto v___jp_4909_;
}
v___jp_4909_:
{
lean_object* v___x_4918_; 
lean_inc(v_snd_4911_);
lean_inc(v_snd_4908_);
v___x_4918_ = l_Lean_Elab_Term_elabTerm(v_snd_4908_, v_snd_4911_, v___x_4904_, v___x_4904_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_a_4919_);
lean_dec_ref_known(v___x_4918_, 1);
v___x_4920_ = lean_box(0);
v___x_4921_ = l_Lean_Elab_Term_ensureHasType(v_snd_4911_, v_a_4919_, v___x_4920_, v___x_4920_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4923_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
v___x_4923_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4910_);
if (lean_obj_tag(v_fst_4907_) == 0)
{
v___y_4890_ = v_fst_4910_;
v___y_4891_ = v___x_4923_;
v___y_4892_ = v_a_4922_;
v___y_4893_ = v___x_4920_;
goto v___jp_4889_;
}
else
{
lean_object* v_val_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4932_; 
v_val_4924_ = lean_ctor_get(v_fst_4907_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v_fst_4907_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4926_ = v_fst_4907_;
v_isShared_4927_ = v_isSharedCheck_4932_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_val_4924_);
lean_dec(v_fst_4907_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4932_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4928_ = l_Lean_TSyntax_getId(v_val_4924_);
lean_dec(v_val_4924_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4928_);
v___x_4930_ = v___x_4926_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4928_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
v___y_4890_ = v_fst_4910_;
v___y_4891_ = v___x_4923_;
v___y_4892_ = v_a_4922_;
v___y_4893_ = v___x_4930_;
goto v___jp_4889_;
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec_ref(v_fst_4910_);
lean_dec(v_fst_4907_);
lean_dec_ref(v_cs_4881_);
lean_dec(v_i_4880_);
v_a_4933_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4921_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4921_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_snd_4911_);
lean_dec_ref(v_fst_4910_);
lean_dec(v_fst_4907_);
lean_dec_ref(v_cs_4881_);
lean_dec(v_i_4880_);
v_a_4941_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4918_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4918_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
}
v___jp_4889_:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4894_, 0, v___y_4892_);
lean_ctor_set(v___x_4894_, 1, v___y_4891_);
lean_ctor_set(v___x_4894_, 2, v___y_4893_);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___y_4890_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_unsigned_to_nat(1u);
v___x_4897_ = lean_nat_add(v_i_4880_, v___x_4896_);
lean_dec(v_i_4880_);
v___x_4898_ = lean_array_push(v_cs_4881_, v___x_4895_);
v_i_4880_ = v___x_4897_;
v_cs_4881_ = v___x_4898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_4991_, lean_object* v_bs_4992_, lean_object* v_i_4993_, lean_object* v_cs_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_4991_, v_bs_4992_, v_i_4993_, v_cs_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec_ref(v_bs_4992_);
lean_dec_ref(v_as_4991_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5005_, lean_object* v_g_5006_, lean_object* v_pats_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5015_ = lean_array_mk(v_pats_5007_);
v___x_5016_ = lean_unsigned_to_nat(0u);
v___x_5017_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5018_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5005_, v___x_5015_, v___x_5016_, v___x_5017_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
lean_dec_ref(v___x_5015_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5020_; lean_object* v_fst_5021_; lean_object* v_snd_5022_; lean_object* v___x_5023_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref_known(v___x_5018_, 1);
v___x_5020_ = l_Array_unzip___redArg(v_a_5019_);
lean_dec(v_a_5019_);
v_fst_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_fst_5021_);
v_snd_5022_ = lean_ctor_get(v___x_5020_, 1);
lean_inc(v_snd_5022_);
lean_dec_ref(v___x_5020_);
v___x_5023_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5006_, v_snd_5022_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
lean_dec(v_snd_5022_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v_snd_5025_; lean_object* v_fst_5026_; lean_object* v_fst_5027_; lean_object* v_snd_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___x_5023_, 1);
v_snd_5025_ = lean_ctor_get(v_a_5024_, 1);
lean_inc(v_snd_5025_);
v_fst_5026_ = lean_ctor_get(v_a_5024_, 0);
lean_inc(v_fst_5026_);
lean_dec(v_a_5024_);
v_fst_5027_ = lean_ctor_get(v_snd_5025_, 0);
lean_inc(v_fst_5027_);
v_snd_5028_ = lean_ctor_get(v_snd_5025_, 1);
lean_inc(v_snd_5028_);
lean_dec(v_snd_5025_);
v___x_5029_ = lean_array_get_size(v_tgts_5005_);
v___x_5030_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5005_, v___x_5016_, v___x_5029_);
v___x_5031_ = l_Array_zip___redArg(v___x_5030_, v_fst_5027_);
lean_dec(v_fst_5027_);
lean_dec_ref(v___x_5030_);
v___x_5032_ = lean_box(0);
v___x_5033_ = l_Array_zip___redArg(v_fst_5021_, v_fst_5026_);
lean_dec(v_fst_5026_);
lean_dec(v_fst_5021_);
v___x_5034_ = lean_array_to_list(v___x_5033_);
v___x_5035_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5035_, 0, v___x_5031_);
v___x_5036_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5028_, v___x_5032_, v___x_5017_, v___x_5017_, v___x_5034_, v___x_5035_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5045_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5045_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5045_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5041_; lean_object* v___x_5043_; 
v___x_5041_ = lean_array_to_list(v_a_5037_);
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5041_);
v___x_5043_ = v___x_5039_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
else
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
v_a_5046_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_5036_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5036_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_dec(v_fst_5021_);
v_a_5054_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_5023_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5023_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
else
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5069_; 
lean_dec(v_g_5006_);
v_a_5062_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5064_ = v___x_5018_;
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5018_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5070_, lean_object* v_g_5071_, lean_object* v_pats_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5070_, v_g_5071_, v_pats_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec_ref(v_tgts_5070_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5081_, size_t v_sz_5082_, size_t v_i_5083_, lean_object* v_bs_5084_){
_start:
{
uint8_t v___x_5085_; 
v___x_5085_ = lean_usize_dec_lt(v_i_5083_, v_sz_5082_);
if (v___x_5085_ == 0)
{
return v_bs_5084_;
}
else
{
lean_object* v___x_5086_; uint8_t v___x_5087_; lean_object* v___x_5088_; lean_object* v_bs_x27_5089_; uint8_t v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; size_t v___x_5093_; size_t v___x_5094_; lean_object* v___x_5095_; 
v___x_5086_ = lean_unsigned_to_nat(1u);
v___x_5087_ = lean_nat_dec_eq(v___x_5081_, v___x_5086_);
v___x_5088_ = lean_unsigned_to_nat(0u);
v_bs_x27_5089_ = lean_array_uset(v_bs_5084_, v_i_5083_, v___x_5088_);
v___x_5090_ = 0;
v___x_5091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_5092_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1, v___x_5090_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 1, v___x_5087_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 2, v___x_5087_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 3, v___x_5087_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 4, v___x_5087_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 5, v___x_5087_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1 + 6, v___x_5087_);
v___x_5093_ = ((size_t)1ULL);
v___x_5094_ = lean_usize_add(v_i_5083_, v___x_5093_);
v___x_5095_ = lean_array_uset(v_bs_x27_5089_, v_i_5083_, v___x_5092_);
v_i_5083_ = v___x_5094_;
v_bs_5084_ = v___x_5095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5097_, lean_object* v_sz_5098_, lean_object* v_i_5099_, lean_object* v_bs_5100_){
_start:
{
size_t v_sz_boxed_5101_; size_t v_i_boxed_5102_; lean_object* v_res_5103_; 
v_sz_boxed_5101_ = lean_unbox_usize(v_sz_5098_);
lean_dec(v_sz_5098_);
v_i_boxed_5102_ = lean_unbox_usize(v_i_5099_);
lean_dec(v_i_5099_);
v_res_5103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5097_, v_sz_boxed_5101_, v_i_boxed_5102_, v_bs_5100_);
lean_dec(v___x_5097_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5104_, lean_object* v___x_5105_, lean_object* v_pat_5106_, lean_object* v_tgts_5107_, lean_object* v___x_5108_, lean_object* v___f_5109_, lean_object* v_g_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
if (v___x_5104_ == 0)
{
lean_object* v___x_5118_; uint8_t v___x_5119_; lean_object* v___y_5121_; 
lean_dec(v_g_5110_);
v___x_5118_ = lean_unsigned_to_nat(1u);
v___x_5119_ = lean_nat_dec_eq(v___x_5105_, v___x_5118_);
if (v___x_5119_ == 0)
{
lean_object* v_ref_5130_; 
v_ref_5130_ = lean_ctor_get(v_pat_5106_, 0);
lean_inc(v_ref_5130_);
v___y_5121_ = v_ref_5130_;
goto v___jp_5120_;
}
else
{
lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
lean_dec_ref(v_tgts_5107_);
v___x_5131_ = lean_box(0);
v___x_5132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5132_, 0, v_pat_5106_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
lean_inc(v___y_5116_);
lean_inc_ref(v___y_5115_);
lean_inc(v___y_5114_);
lean_inc_ref(v___y_5113_);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
v___x_5133_ = lean_apply_8(v___f_5109_, v___x_5132_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, lean_box(0));
return v___x_5133_;
}
v___jp_5120_:
{
lean_object* v___x_5122_; lean_object* v_snd_5123_; size_t v_sz_5124_; size_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v_snd_5128_; lean_object* v___x_5129_; 
v___x_5122_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5106_);
v_snd_5123_ = lean_ctor_get(v___x_5122_, 1);
lean_inc(v_snd_5123_);
lean_dec_ref(v___x_5122_);
v_sz_5124_ = lean_array_size(v_tgts_5107_);
v___x_5125_ = ((size_t)0ULL);
v___x_5126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5105_, v_sz_5124_, v___x_5125_, v_tgts_5107_);
v___x_5127_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5121_, v___x_5126_, v___x_5119_, v___x_5108_, v_snd_5123_);
lean_dec_ref(v___x_5126_);
v_snd_5128_ = lean_ctor_get(v___x_5127_, 1);
lean_inc(v_snd_5128_);
lean_dec_ref(v___x_5127_);
lean_inc(v___y_5116_);
lean_inc_ref(v___y_5115_);
lean_inc(v___y_5114_);
lean_inc_ref(v___y_5113_);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
v___x_5129_ = lean_apply_8(v___f_5109_, v_snd_5128_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, lean_box(0));
return v___x_5129_;
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
lean_dec_ref(v___f_5109_);
lean_dec_ref(v_tgts_5107_);
lean_dec_ref(v_pat_5106_);
v___x_5134_ = lean_box(0);
v___x_5135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5135_, 0, v_g_5110_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
v___x_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5135_);
return v___x_5136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5137_, lean_object* v___x_5138_, lean_object* v_pat_5139_, lean_object* v_tgts_5140_, lean_object* v___x_5141_, lean_object* v___f_5142_, lean_object* v_g_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
uint8_t v___x_5055__boxed_5151_; lean_object* v_res_5152_; 
v___x_5055__boxed_5151_ = lean_unbox(v___x_5137_);
v_res_5152_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5055__boxed_5151_, v___x_5138_, v_pat_5139_, v_tgts_5140_, v___x_5141_, v___f_5142_, v_g_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v___y_5147_);
lean_dec_ref(v___y_5146_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___x_5141_);
lean_dec(v___x_5138_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5153_, lean_object* v_pat_5154_, lean_object* v_g_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
lean_object* v___f_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; lean_object* v___y_5168_; uint8_t v___x_5169_; lean_object* v___x_5170_; 
lean_inc(v_g_5155_);
lean_inc_ref(v_tgts_5153_);
v___f_5163_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5163_, 0, v_tgts_5153_);
lean_closure_set(v___f_5163_, 1, v_g_5155_);
v___x_5164_ = lean_array_get_size(v_tgts_5153_);
v___x_5165_ = lean_unsigned_to_nat(0u);
v___x_5166_ = lean_nat_dec_eq(v___x_5164_, v___x_5165_);
v___x_5167_ = lean_box(v___x_5166_);
v___y_5168_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5168_, 0, v___x_5167_);
lean_closure_set(v___y_5168_, 1, v___x_5164_);
lean_closure_set(v___y_5168_, 2, v_pat_5154_);
lean_closure_set(v___y_5168_, 3, v_tgts_5153_);
lean_closure_set(v___y_5168_, 4, v___x_5165_);
lean_closure_set(v___y_5168_, 5, v___f_5163_);
lean_closure_set(v___y_5168_, 6, v_g_5155_);
v___x_5169_ = 1;
v___x_5170_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5168_, v___x_5169_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5171_, lean_object* v_pat_5172_, lean_object* v_g_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5171_, v_pat_5172_, v_g_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5186_, lean_object* v_g_5187_, lean_object* v_pat_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Lean_Elab_Term_elabType(v_ty_5186_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc_n(v_a_5197_, 2);
lean_dec_ref_known(v___x_5196_, 1);
v___x_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5198_, 0, v_a_5197_);
v___x_5199_ = 0;
v___x_5200_ = lean_box(0);
v___x_5201_ = l_Lean_Meta_mkFreshExprMVar(v___x_5198_, v___x_5199_, v___x_5200_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___y_5204_; lean_object* v___x_5258_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref_known(v___x_5201_, 1);
v___x_5258_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5188_);
if (lean_obj_tag(v___x_5258_) == 0)
{
v___y_5204_ = v___x_5200_;
goto v___jp_5203_;
}
else
{
lean_object* v_val_5259_; 
v_val_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_val_5259_);
lean_dec_ref_known(v___x_5258_, 1);
v___y_5204_ = v_val_5259_;
goto v___jp_5203_;
}
v___jp_5203_:
{
lean_object* v___x_5205_; 
lean_inc(v_a_5202_);
v___x_5205_ = l_Lean_MVarId_assert(v_g_5187_, v___y_5204_, v_a_5197_, v_a_5202_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v_a_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_a_5206_);
lean_dec_ref_known(v___x_5205_, 1);
v___x_5207_ = 0;
v___x_5208_ = l_Lean_Meta_intro1Core(v_a_5206_, v___x_5207_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v_fst_5210_; lean_object* v_snd_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5241_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref_known(v___x_5208_, 1);
v_fst_5210_ = lean_ctor_get(v_a_5209_, 0);
v_snd_5211_ = lean_ctor_get(v_a_5209_, 1);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_a_5209_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5213_ = v_a_5209_;
v_isShared_5214_ = v_isSharedCheck_5241_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_snd_5211_);
lean_inc(v_fst_5210_);
lean_dec(v_a_5209_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5241_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5215_ = lean_box(0);
v___x_5216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5217_ = l_Lean_Expr_fvar___override(v_fst_5210_);
v___x_5218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5219_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5211_, v___x_5215_, v___x_5216_, v___x_5217_, v___x_5216_, v_pat_5188_, v___x_5218_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
lean_dec_ref(v___x_5217_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5232_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5222_ = v___x_5219_;
v_isShared_5223_ = v_isSharedCheck_5232_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5219_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5232_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5227_; 
v___x_5224_ = l_Lean_Expr_mvarId_x21(v_a_5202_);
lean_dec(v_a_5202_);
v___x_5225_ = lean_array_to_list(v_a_5220_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set_tag(v___x_5213_, 1);
lean_ctor_set(v___x_5213_, 1, v___x_5225_);
lean_ctor_set(v___x_5213_, 0, v___x_5224_);
v___x_5227_ = v___x_5213_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5231_, 1, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5229_; 
if (v_isShared_5223_ == 0)
{
lean_ctor_set(v___x_5222_, 0, v___x_5227_);
v___x_5229_ = v___x_5222_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_del_object(v___x_5213_);
lean_dec(v_a_5202_);
v_a_5233_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5219_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5219_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_dec(v_a_5202_);
lean_dec_ref(v_pat_5188_);
v_a_5242_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5208_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5208_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_dec(v_a_5202_);
lean_dec_ref(v_pat_5188_);
v_a_5250_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5205_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5205_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_dec(v_a_5197_);
lean_dec_ref(v_pat_5188_);
lean_dec(v_g_5187_);
v_a_5260_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5201_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5201_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5275_; 
lean_dec_ref(v_pat_5188_);
lean_dec(v_g_5187_);
v_a_5268_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5270_ = v___x_5196_;
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5196_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5276_, lean_object* v_g_5277_, lean_object* v_pat_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5276_, v_g_5277_, v_pat_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5287_, lean_object* v_ty_5288_, lean_object* v_g_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_){
_start:
{
lean_object* v___f_5297_; uint8_t v___x_5298_; lean_object* v___x_5299_; 
v___f_5297_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5297_, 0, v_ty_5288_);
lean_closure_set(v___f_5297_, 1, v_g_5289_);
lean_closure_set(v___f_5297_, 2, v_pat_5287_);
v___x_5298_ = 1;
v___x_5299_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5297_, v___x_5298_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5300_, lean_object* v_ty_5301_, lean_object* v_g_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5300_, v_ty_5301_, v_g_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_a_5306_);
lean_dec_ref(v_a_5305_);
lean_dec(v_a_5304_);
lean_dec_ref(v_a_5303_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5321_, lean_object* v_acc_5322_, lean_object* v_ty_x3f_5323_){
_start:
{
lean_object* v___x_5324_; uint8_t v___x_5325_; 
v___x_5324_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5321_);
v___x_5325_ = l_Lean_Syntax_isOfKind(v_pat_5321_, v___x_5324_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5326_; uint8_t v___x_5327_; 
v___x_5326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5321_);
v___x_5327_ = l_Lean_Syntax_isOfKind(v_pat_5321_, v___x_5326_);
if (v___x_5327_ == 0)
{
lean_dec(v_ty_x3f_5323_);
lean_dec(v_pat_5321_);
return v_acc_5322_;
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; 
v___x_5328_ = lean_unsigned_to_nat(1u);
v___x_5329_ = l_Lean_Syntax_getArg(v_pat_5321_, v___x_5328_);
v___x_5330_ = lean_unsigned_to_nat(2u);
v___x_5331_ = l_Lean_Syntax_getArg(v_pat_5321_, v___x_5330_);
lean_dec(v_pat_5321_);
v___x_5332_ = l_Lean_Syntax_isNone(v___x_5331_);
if (v___x_5332_ == 0)
{
uint8_t v___x_5333_; 
lean_dec(v_ty_x3f_5323_);
lean_inc(v___x_5331_);
v___x_5333_ = l_Lean_Syntax_matchesNull(v___x_5331_, v___x_5330_);
if (v___x_5333_ == 0)
{
lean_dec(v___x_5331_);
lean_dec(v___x_5329_);
return v_acc_5322_;
}
else
{
lean_object* v_ty_x3f_x27_5334_; lean_object* v___x_5335_; lean_object* v_pats_5336_; lean_object* v___x_5337_; 
v_ty_x3f_x27_5334_ = l_Lean_Syntax_getArg(v___x_5331_, v___x_5328_);
lean_dec(v___x_5331_);
v___x_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5335_, 0, v_ty_x3f_x27_5334_);
v_pats_5336_ = l_Lean_Syntax_getArgs(v___x_5329_);
lean_dec(v___x_5329_);
v___x_5337_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5336_, v_acc_5322_, v___x_5335_);
lean_dec_ref(v_pats_5336_);
return v___x_5337_;
}
}
else
{
lean_object* v_pats_5338_; lean_object* v___x_5339_; 
lean_dec(v___x_5331_);
v_pats_5338_ = l_Lean_Syntax_getArgs(v___x_5329_);
lean_dec(v___x_5329_);
v___x_5339_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5338_, v_acc_5322_, v_ty_x3f_5323_);
lean_dec_ref(v_pats_5338_);
return v___x_5339_;
}
}
}
else
{
lean_object* v___x_5340_; lean_object* v_p_5341_; 
v___x_5340_ = lean_unsigned_to_nat(0u);
v_p_5341_ = l_Lean_Syntax_getArg(v_pat_5321_, v___x_5340_);
lean_dec(v_pat_5321_);
if (lean_obj_tag(v_ty_x3f_5323_) == 0)
{
lean_object* v___x_5342_; 
v___x_5342_ = lean_array_push(v_acc_5322_, v_p_5341_);
return v___x_5342_;
}
else
{
lean_object* v_val_5343_; lean_object* v___x_5344_; lean_object* v_ref_5345_; uint8_t v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; 
v_val_5343_ = lean_ctor_get(v_ty_x3f_5323_, 0);
lean_inc(v_val_5343_);
lean_dec_ref_known(v_ty_x3f_5323_, 1);
v___x_5344_ = lean_box(0);
v_ref_5345_ = l_Lean_replaceRef(v_p_5341_, v___x_5344_);
v___x_5346_ = 0;
v___x_5347_ = l_Lean_SourceInfo_fromRef(v_ref_5345_, v___x_5346_);
lean_dec(v_ref_5345_);
v___x_5348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5347_, 7);
v___x_5350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5350_, 0, v___x_5347_);
lean_ctor_set(v___x_5350_, 1, v___x_5349_);
v___x_5351_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5352_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5353_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5354_ = l_Lean_Syntax_node1(v___x_5347_, v___x_5353_, v_p_5341_);
v___x_5355_ = l_Lean_Syntax_node1(v___x_5347_, v___x_5352_, v___x_5354_);
v___x_5356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5347_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
v___x_5358_ = l_Lean_Syntax_node2(v___x_5347_, v___x_5353_, v___x_5357_, v_val_5343_);
v___x_5359_ = l_Lean_Syntax_node2(v___x_5347_, v___x_5351_, v___x_5355_, v___x_5358_);
v___x_5360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5347_);
lean_ctor_set(v___x_5361_, 1, v___x_5360_);
v___x_5362_ = l_Lean_Syntax_node3(v___x_5347_, v___x_5348_, v___x_5350_, v___x_5359_, v___x_5361_);
v___x_5363_ = lean_array_push(v_acc_5322_, v___x_5362_);
return v___x_5363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5364_, lean_object* v_as_5365_, size_t v_i_5366_, size_t v_stop_5367_, lean_object* v_b_5368_){
_start:
{
uint8_t v___x_5369_; 
v___x_5369_ = lean_usize_dec_eq(v_i_5366_, v_stop_5367_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; lean_object* v___x_5371_; size_t v___x_5372_; size_t v___x_5373_; 
v___x_5370_ = lean_array_uget_borrowed(v_as_5365_, v_i_5366_);
lean_inc(v_ty_x3f_5364_);
lean_inc(v___x_5370_);
v___x_5371_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5370_, v_b_5368_, v_ty_x3f_5364_);
v___x_5372_ = ((size_t)1ULL);
v___x_5373_ = lean_usize_add(v_i_5366_, v___x_5372_);
v_i_5366_ = v___x_5373_;
v_b_5368_ = v___x_5371_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5364_);
return v_b_5368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5375_, lean_object* v_acc_5376_, lean_object* v_ty_x3f_5377_){
_start:
{
lean_object* v___x_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v___x_5378_ = lean_unsigned_to_nat(0u);
v___x_5379_ = lean_array_get_size(v_pats_5375_);
v___x_5380_ = lean_nat_dec_lt(v___x_5378_, v___x_5379_);
if (v___x_5380_ == 0)
{
lean_dec(v_ty_x3f_5377_);
return v_acc_5376_;
}
else
{
size_t v___x_5381_; size_t v___x_5382_; lean_object* v___x_5383_; 
v___x_5381_ = ((size_t)0ULL);
v___x_5382_ = lean_usize_of_nat(v___x_5379_);
v___x_5383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5377_, v_pats_5375_, v___x_5381_, v___x_5382_, v_acc_5376_);
return v___x_5383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5384_, lean_object* v_acc_5385_, lean_object* v_ty_x3f_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5384_, v_acc_5385_, v_ty_x3f_5386_);
lean_dec_ref(v_pats_5384_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5388_, lean_object* v_as_5389_, lean_object* v_i_5390_, lean_object* v_stop_5391_, lean_object* v_b_5392_){
_start:
{
size_t v_i_boxed_5393_; size_t v_stop_boxed_5394_; lean_object* v_res_5395_; 
v_i_boxed_5393_ = lean_unbox_usize(v_i_5390_);
lean_dec(v_i_5390_);
v_stop_boxed_5394_ = lean_unbox_usize(v_stop_5391_);
lean_dec(v_stop_5391_);
v_res_5395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5388_, v_as_5389_, v_i_boxed_5393_, v_stop_boxed_5394_, v_b_5392_);
lean_dec_ref(v_as_5389_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5397_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5401_, lean_object* v_pats_5402_, lean_object* v_ty_x3f_5403_, lean_object* v_cont_5404_, lean_object* v_i_5405_, lean_object* v_g_5406_, lean_object* v_fs_5407_, lean_object* v_clears_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5401_, v_pats_5402_, v_ty_x3f_5403_, v_cont_5404_, v_i_5405_, v_g_5406_, v_fs_5407_, v_clears_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
lean_dec(v_a_5413_);
lean_dec_ref(v_a_5412_);
lean_dec(v_a_5411_);
lean_dec_ref(v_a_5410_);
lean_dec(v_i_5405_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5418_ = _args[0];
lean_object* v_ref_5419_ = _args[1];
lean_object* v_pats_5420_ = _args[2];
lean_object* v_ty_x3f_5421_ = _args[3];
lean_object* v_cont_5422_ = _args[4];
lean_object* v_i_5423_ = _args[5];
lean_object* v_g_5424_ = _args[6];
lean_object* v_fs_5425_ = _args[7];
lean_object* v_clears_5426_ = _args[8];
lean_object* v_a_5427_ = _args[9];
lean_object* v_a_5428_ = _args[10];
lean_object* v_a_5429_ = _args[11];
lean_object* v_a_5430_ = _args[12];
lean_object* v_a_5431_ = _args[13];
lean_object* v_a_5432_ = _args[14];
lean_object* v_a_5433_ = _args[15];
lean_object* v_a_5434_ = _args[16];
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5418_, v_ref_5419_, v_pats_5420_, v_ty_x3f_5421_, v_cont_5422_, v_i_5423_, v_g_5424_, v_fs_5425_, v_clears_5426_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
lean_dec(v_a_5431_);
lean_dec_ref(v_a_5430_);
lean_dec(v_a_5429_);
lean_dec_ref(v_a_5428_);
lean_dec(v_i_5423_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5436_, lean_object* v_fs_5437_, lean_object* v_clears_5438_, lean_object* v_ref_5439_, lean_object* v_pats_5440_, lean_object* v_ty_x3f_5441_, lean_object* v_a_5442_, lean_object* v_cont_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5451_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5436_);
v___x_5452_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5452_, 0, lean_box(0));
lean_closure_set(v___x_5452_, 1, v_ref_5439_);
lean_closure_set(v___x_5452_, 2, v_pats_5440_);
lean_closure_set(v___x_5452_, 3, v_ty_x3f_5441_);
lean_closure_set(v___x_5452_, 4, v_cont_5443_);
lean_closure_set(v___x_5452_, 5, v___x_5451_);
lean_closure_set(v___x_5452_, 6, v_g_5436_);
lean_closure_set(v___x_5452_, 7, v_fs_5437_);
lean_closure_set(v___x_5452_, 8, v_clears_5438_);
lean_closure_set(v___x_5452_, 9, v_a_5442_);
v___x_5453_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5436_, v___x_5452_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5454_, lean_object* v_fs_5455_, lean_object* v_clears_5456_, lean_object* v_a_5457_, lean_object* v_ref_5458_, lean_object* v_pat_5459_, lean_object* v_ty_x3f_5460_, lean_object* v_cont_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___y_5470_; lean_object* v___y_5471_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5474_; lean_object* v___y_5475_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___x_5481_; uint8_t v___x_5482_; 
v___x_5481_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5459_);
v___x_5482_ = l_Lean_Syntax_isOfKind(v_pat_5459_, v___x_5481_);
if (v___x_5482_ == 0)
{
lean_object* v___x_5483_; uint8_t v___x_5484_; 
lean_dec(v_ref_5458_);
v___x_5483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5459_);
v___x_5484_ = l_Lean_Syntax_isOfKind(v_pat_5459_, v___x_5483_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5485_; 
lean_dec_ref(v_cont_5461_);
lean_dec(v_ty_x3f_5460_);
lean_dec(v_pat_5459_);
lean_dec(v_a_5457_);
lean_dec_ref(v_clears_5456_);
lean_dec(v_fs_5455_);
lean_dec(v_g_5454_);
v___x_5485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5485_;
}
else
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v_ty_x3f_x27_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___x_5500_; lean_object* v___x_5501_; uint8_t v___x_5502_; 
v___x_5486_ = lean_unsigned_to_nat(1u);
v___x_5487_ = l_Lean_Syntax_getArg(v_pat_5459_, v___x_5486_);
v___x_5500_ = lean_unsigned_to_nat(2u);
v___x_5501_ = l_Lean_Syntax_getArg(v_pat_5459_, v___x_5500_);
v___x_5502_ = l_Lean_Syntax_isNone(v___x_5501_);
if (v___x_5502_ == 0)
{
uint8_t v___x_5503_; 
lean_inc(v___x_5501_);
v___x_5503_ = l_Lean_Syntax_matchesNull(v___x_5501_, v___x_5500_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
lean_dec(v___x_5501_);
lean_dec(v___x_5487_);
lean_dec_ref(v_cont_5461_);
lean_dec(v_ty_x3f_5460_);
lean_dec(v_pat_5459_);
lean_dec(v_a_5457_);
lean_dec_ref(v_clears_5456_);
lean_dec(v_fs_5455_);
lean_dec(v_g_5454_);
v___x_5504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5504_;
}
else
{
lean_object* v_ty_x3f_x27_5505_; lean_object* v___x_5506_; 
v_ty_x3f_x27_5505_ = l_Lean_Syntax_getArg(v___x_5501_, v___x_5486_);
lean_dec(v___x_5501_);
v___x_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5506_, 0, v_ty_x3f_x27_5505_);
v_ty_x3f_x27_5489_ = v___x_5506_;
v___y_5490_ = v_a_5462_;
v___y_5491_ = v_a_5463_;
v___y_5492_ = v_a_5464_;
v___y_5493_ = v_a_5465_;
v___y_5494_ = v_a_5466_;
v___y_5495_ = v_a_5467_;
goto v___jp_5488_;
}
}
else
{
lean_object* v___x_5507_; 
lean_dec(v___x_5501_);
v___x_5507_ = lean_box(0);
v_ty_x3f_x27_5489_ = v___x_5507_;
v___y_5490_ = v_a_5462_;
v___y_5491_ = v_a_5463_;
v___y_5492_ = v_a_5464_;
v___y_5493_ = v_a_5465_;
v___y_5494_ = v_a_5466_;
v___y_5495_ = v_a_5467_;
goto v___jp_5488_;
}
v___jp_5488_:
{
lean_object* v_pats_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; 
v_pats_5496_ = l_Lean_Syntax_getArgs(v___x_5487_);
lean_dec(v___x_5487_);
v___x_5497_ = lean_array_get_size(v_pats_5496_);
v___x_5498_ = lean_nat_dec_eq(v___x_5497_, v___x_5486_);
if (v___x_5498_ == 0)
{
lean_object* v___x_5499_; 
lean_dec(v_pat_5459_);
v___x_5499_ = lean_box(0);
v___y_5470_ = v___y_5490_;
v___y_5471_ = v_ty_x3f_x27_5489_;
v___y_5472_ = v___y_5494_;
v___y_5473_ = v_pats_5496_;
v___y_5474_ = v___y_5491_;
v___y_5475_ = v___y_5493_;
v___y_5476_ = v___y_5492_;
v___y_5477_ = v___y_5495_;
v___y_5478_ = v___x_5499_;
goto v___jp_5469_;
}
else
{
v___y_5470_ = v___y_5490_;
v___y_5471_ = v_ty_x3f_x27_5489_;
v___y_5472_ = v___y_5494_;
v___y_5473_ = v_pats_5496_;
v___y_5474_ = v___y_5491_;
v___y_5475_ = v___y_5493_;
v___y_5476_ = v___y_5492_;
v___y_5477_ = v___y_5495_;
v___y_5478_ = v_pat_5459_;
goto v___jp_5469_;
}
}
}
}
else
{
lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5508_ = lean_unsigned_to_nat(0u);
v___x_5509_ = l_Lean_Syntax_getArg(v_pat_5459_, v___x_5508_);
lean_dec(v_pat_5459_);
v___x_5510_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5509_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_object* v_a_5511_; lean_object* v___x_5512_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5540_; lean_object* v_ref_5544_; 
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
lean_inc(v_a_5511_);
lean_dec_ref_known(v___x_5510_, 1);
v___x_5512_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5458_, v_a_5511_, v_ty_x3f_5460_);
lean_dec(v_ty_x3f_5460_);
v_ref_5544_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_ref_5544_);
v___y_5540_ = v_ref_5544_;
goto v___jp_5539_;
v___jp_5513_:
{
lean_object* v_toCold_5516_; lean_object* v_currRecDepth_5517_; lean_object* v_ref_5518_; uint16_t v_optionFlags_5519_; uint8_t v_suppressElabErrors_5520_; uint8_t v_checkDeprecated_5521_; uint8_t v_isRecordingDeps_5522_; lean_object* v_ref_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v_toCold_5516_ = lean_ctor_get(v_a_5466_, 0);
v_currRecDepth_5517_ = lean_ctor_get(v_a_5466_, 1);
v_ref_5518_ = lean_ctor_get(v_a_5466_, 2);
v_optionFlags_5519_ = lean_ctor_get_uint16(v_a_5466_, sizeof(void*)*3);
v_suppressElabErrors_5520_ = lean_ctor_get_uint8(v_a_5466_, sizeof(void*)*3 + 2);
v_checkDeprecated_5521_ = lean_ctor_get_uint8(v_a_5466_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5522_ = lean_ctor_get_uint8(v_a_5466_, sizeof(void*)*3 + 4);
v_ref_5523_ = l_Lean_replaceRef(v___y_5514_, v_ref_5518_);
lean_dec(v___y_5514_);
lean_inc(v_currRecDepth_5517_);
lean_inc_ref(v_toCold_5516_);
v___x_5524_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5524_, 0, v_toCold_5516_);
lean_ctor_set(v___x_5524_, 1, v_currRecDepth_5517_);
lean_ctor_set(v___x_5524_, 2, v_ref_5523_);
lean_ctor_set_uint16(v___x_5524_, sizeof(void*)*3, v_optionFlags_5519_);
lean_ctor_set_uint8(v___x_5524_, sizeof(void*)*3 + 2, v_suppressElabErrors_5520_);
lean_ctor_set_uint8(v___x_5524_, sizeof(void*)*3 + 3, v_checkDeprecated_5521_);
lean_ctor_set_uint8(v___x_5524_, sizeof(void*)*3 + 4, v_isRecordingDeps_5522_);
v___x_5525_ = l_Lean_MVarId_intro(v_g_5454_, v___y_5515_, v_a_5464_, v_a_5465_, v___x_5524_, v_a_5467_);
lean_dec_ref_known(v___x_5524_, 3);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_object* v_a_5526_; lean_object* v_fst_5527_; lean_object* v_snd_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; 
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
lean_inc(v_a_5526_);
lean_dec_ref_known(v___x_5525_, 1);
v_fst_5527_ = lean_ctor_get(v_a_5526_, 0);
lean_inc(v_fst_5527_);
v_snd_5528_ = lean_ctor_get(v_a_5526_, 1);
lean_inc(v_snd_5528_);
lean_dec(v_a_5526_);
v___x_5529_ = l_Lean_Expr_fvar___override(v_fst_5527_);
v___x_5530_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5528_, v_fs_5455_, v_clears_5456_, v___x_5529_, v_a_5457_, v___x_5512_, v_cont_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
lean_dec_ref(v___x_5529_);
return v___x_5530_;
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec_ref(v___x_5512_);
lean_dec_ref(v_cont_5461_);
lean_dec(v_a_5457_);
lean_dec_ref(v_clears_5456_);
lean_dec(v_fs_5455_);
v_a_5531_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5525_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5525_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
v___jp_5539_:
{
lean_object* v___x_5541_; 
v___x_5541_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5512_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v___x_5542_; 
v___x_5542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5514_ = v___y_5540_;
v___y_5515_ = v___x_5542_;
goto v___jp_5513_;
}
else
{
lean_object* v_val_5543_; 
v_val_5543_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_val_5543_);
lean_dec_ref_known(v___x_5541_, 1);
v___y_5514_ = v___y_5540_;
v___y_5515_ = v_val_5543_;
goto v___jp_5513_;
}
}
}
else
{
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
lean_dec_ref(v_cont_5461_);
lean_dec(v_ty_x3f_5460_);
lean_dec(v_ref_5458_);
lean_dec(v_a_5457_);
lean_dec_ref(v_clears_5456_);
lean_dec(v_fs_5455_);
lean_dec(v_g_5454_);
v_a_5545_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5510_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5510_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
v___jp_5469_:
{
if (lean_obj_tag(v___y_5471_) == 0)
{
lean_object* v___x_5479_; 
v___x_5479_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5454_, v_fs_5455_, v_clears_5456_, v___y_5478_, v___y_5473_, v_ty_x3f_5460_, v_a_5457_, v_cont_5461_, v___y_5470_, v___y_5474_, v___y_5476_, v___y_5475_, v___y_5472_, v___y_5477_);
return v___x_5479_;
}
else
{
lean_object* v___x_5480_; 
lean_dec(v_ty_x3f_5460_);
v___x_5480_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5454_, v_fs_5455_, v_clears_5456_, v___y_5478_, v___y_5473_, v___y_5471_, v_a_5457_, v_cont_5461_, v___y_5470_, v___y_5474_, v___y_5476_, v___y_5475_, v___y_5472_, v___y_5477_);
return v___x_5480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5553_, lean_object* v_pats_5554_, lean_object* v_ty_x3f_5555_, lean_object* v_cont_5556_, lean_object* v_i_5557_, lean_object* v_g_5558_, lean_object* v_fs_5559_, lean_object* v_clears_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_){
_start:
{
lean_object* v___x_5569_; uint8_t v___x_5570_; 
v___x_5569_ = lean_array_get_size(v_pats_5554_);
v___x_5570_ = lean_nat_dec_lt(v_i_5557_, v___x_5569_);
if (v___x_5570_ == 0)
{
lean_object* v___x_5571_; 
lean_dec(v_ty_x3f_5555_);
lean_dec_ref(v_pats_5554_);
lean_dec(v_ref_5553_);
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
lean_inc(v_a_5563_);
lean_inc_ref(v_a_5562_);
v___x_5571_ = lean_apply_11(v_cont_5556_, v_g_5558_, v_fs_5559_, v_clears_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, lean_box(0));
return v___x_5571_;
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5572_ = lean_array_fget(v_pats_5554_, v_i_5557_);
v___x_5573_ = lean_unsigned_to_nat(1u);
v___x_5574_ = lean_nat_add(v_i_5557_, v___x_5573_);
lean_inc(v_ty_x3f_5555_);
lean_inc(v_ref_5553_);
v___x_5575_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5575_, 0, v_ref_5553_);
lean_closure_set(v___x_5575_, 1, v_pats_5554_);
lean_closure_set(v___x_5575_, 2, v_ty_x3f_5555_);
lean_closure_set(v___x_5575_, 3, v_cont_5556_);
lean_closure_set(v___x_5575_, 4, v___x_5574_);
v___x_5576_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5558_, v_fs_5559_, v_clears_5560_, v_a_5561_, v_ref_5553_, v___x_5572_, v_ty_x3f_5555_, v___x_5575_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
return v___x_5576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5577_, lean_object* v_ref_5578_, lean_object* v_pats_5579_, lean_object* v_ty_x3f_5580_, lean_object* v_cont_5581_, lean_object* v_i_5582_, lean_object* v_g_5583_, lean_object* v_fs_5584_, lean_object* v_clears_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_){
_start:
{
lean_object* v___x_5594_; 
v___x_5594_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5578_, v_pats_5579_, v_ty_x3f_5580_, v_cont_5581_, v_i_5582_, v_g_5583_, v_fs_5584_, v_clears_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
return v___x_5594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5595_, lean_object* v_fs_5596_, lean_object* v_clears_5597_, lean_object* v_ref_5598_, lean_object* v_pats_5599_, lean_object* v_ty_x3f_5600_, lean_object* v_a_5601_, lean_object* v_cont_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5595_, v_fs_5596_, v_clears_5597_, v_ref_5598_, v_pats_5599_, v_ty_x3f_5600_, v_a_5601_, v_cont_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
lean_dec(v_a_5604_);
lean_dec_ref(v_a_5603_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5611_, lean_object* v_fs_5612_, lean_object* v_clears_5613_, lean_object* v_a_5614_, lean_object* v_ref_5615_, lean_object* v_pat_5616_, lean_object* v_ty_x3f_5617_, lean_object* v_cont_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
lean_object* v_res_5626_; 
v_res_5626_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5611_, v_fs_5612_, v_clears_5613_, v_a_5614_, v_ref_5615_, v_pat_5616_, v_ty_x3f_5617_, v_cont_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
lean_dec(v_a_5624_);
lean_dec_ref(v_a_5623_);
lean_dec(v_a_5622_);
lean_dec_ref(v_a_5621_);
lean_dec(v_a_5620_);
lean_dec_ref(v_a_5619_);
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_){
_start:
{
lean_object* v___x_5635_; 
v___x_5635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
return v_res_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5645_, lean_object* v_g_5646_, lean_object* v_fs_5647_, lean_object* v_clears_5648_, lean_object* v_a_5649_, lean_object* v_ref_5650_, lean_object* v_pat_5651_, lean_object* v_ty_x3f_5652_, lean_object* v_cont_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v___x_5661_; 
v___x_5661_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5646_, v_fs_5647_, v_clears_5648_, v_a_5649_, v_ref_5650_, v_pat_5651_, v_ty_x3f_5652_, v_cont_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
return v___x_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5662_, lean_object* v_g_5663_, lean_object* v_fs_5664_, lean_object* v_clears_5665_, lean_object* v_a_5666_, lean_object* v_ref_5667_, lean_object* v_pat_5668_, lean_object* v_ty_x3f_5669_, lean_object* v_cont_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_){
_start:
{
lean_object* v_res_5678_; 
v_res_5678_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5662_, v_g_5663_, v_fs_5664_, v_clears_5665_, v_a_5666_, v_ref_5667_, v_pat_5668_, v_ty_x3f_5669_, v_cont_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
lean_dec(v_a_5674_);
lean_dec_ref(v_a_5673_);
lean_dec(v_a_5672_);
lean_dec_ref(v_a_5671_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5679_, lean_object* v_g_5680_, lean_object* v_fs_5681_, lean_object* v_clears_5682_, lean_object* v_ref_5683_, lean_object* v_pats_5684_, lean_object* v_ty_x3f_5685_, lean_object* v_a_5686_, lean_object* v_cont_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_){
_start:
{
lean_object* v___x_5695_; 
v___x_5695_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5680_, v_fs_5681_, v_clears_5682_, v_ref_5683_, v_pats_5684_, v_ty_x3f_5685_, v_a_5686_, v_cont_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5696_, lean_object* v_g_5697_, lean_object* v_fs_5698_, lean_object* v_clears_5699_, lean_object* v_ref_5700_, lean_object* v_pats_5701_, lean_object* v_ty_x3f_5702_, lean_object* v_a_5703_, lean_object* v_cont_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5696_, v_g_5697_, v_fs_5698_, v_clears_5699_, v_ref_5700_, v_pats_5701_, v_ty_x3f_5702_, v_a_5703_, v_cont_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
lean_dec(v_a_5706_);
lean_dec_ref(v_a_5705_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5713_, lean_object* v___x_5714_, lean_object* v___x_5715_, lean_object* v___x_5716_, lean_object* v_pats_5717_, lean_object* v_ty_x3f_5718_, lean_object* v___x_5719_, lean_object* v___x_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v___x_5728_; 
v___x_5728_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5713_, v___x_5714_, v___x_5715_, v___x_5716_, v_pats_5717_, v_ty_x3f_5718_, v___x_5719_, v___x_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5737_; 
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5731_ = v___x_5728_;
v_isShared_5732_ = v_isSharedCheck_5737_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5728_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5737_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5733_; lean_object* v___x_5735_; 
v___x_5733_ = lean_array_to_list(v_a_5729_);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 0, v___x_5733_);
v___x_5735_ = v___x_5731_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v___x_5733_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
else
{
lean_object* v_a_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
v_a_5738_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5728_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_a_5738_);
lean_dec(v___x_5728_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_a_5738_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
return v___x_5743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5746_, lean_object* v___x_5747_, lean_object* v___x_5748_, lean_object* v___x_5749_, lean_object* v_pats_5750_, lean_object* v_ty_x3f_5751_, lean_object* v___x_5752_, lean_object* v___x_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5746_, v___x_5747_, v___x_5748_, v___x_5749_, v_pats_5750_, v_ty_x3f_5751_, v___x_5752_, v___x_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5757_);
lean_dec_ref(v___y_5756_);
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5762_, lean_object* v_ty_x3f_5763_, lean_object* v_g_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_){
_start:
{
lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___f_5776_; uint8_t v___x_5777_; lean_object* v___x_5778_; 
v___x_5772_ = lean_box(0);
v___x_5773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5774_ = lean_box(0);
v___x_5775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5776_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5776_, 0, v_g_5764_);
lean_closure_set(v___f_5776_, 1, v___x_5772_);
lean_closure_set(v___f_5776_, 2, v___x_5773_);
lean_closure_set(v___f_5776_, 3, v___x_5774_);
lean_closure_set(v___f_5776_, 4, v_pats_5762_);
lean_closure_set(v___f_5776_, 5, v_ty_x3f_5763_);
lean_closure_set(v___f_5776_, 6, v___x_5773_);
lean_closure_set(v___f_5776_, 7, v___x_5775_);
v___x_5777_ = 1;
v___x_5778_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5776_, v___x_5777_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5779_, lean_object* v_ty_x3f_5780_, lean_object* v_g_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5779_, v_ty_x3f_5780_, v_g_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
lean_dec(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5791_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5792_, 0, v___x_5791_);
return v___x_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5793_){
_start:
{
lean_object* v_res_5794_; 
v_res_5794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
lean_object* v___x_5805_; 
v___x_5805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5807_);
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_){
_start:
{
lean_object* v___x_5827_; 
lean_inc(v___y_5821_);
lean_inc_ref(v___y_5820_);
lean_inc(v___y_5819_);
lean_inc_ref(v___y_5818_);
v___x_5827_ = lean_apply_9(v_x_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, lean_box(0));
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5839_, lean_object* v_x_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
lean_object* v___f_5850_; lean_object* v___x_5851_; 
lean_inc(v___y_5844_);
lean_inc_ref(v___y_5843_);
lean_inc(v___y_5842_);
lean_inc_ref(v___y_5841_);
v___f_5850_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5850_, 0, v_x_5840_);
lean_closure_set(v___f_5850_, 1, v___y_5841_);
lean_closure_set(v___f_5850_, 2, v___y_5842_);
lean_closure_set(v___f_5850_, 3, v___y_5843_);
lean_closure_set(v___f_5850_, 4, v___y_5844_);
v___x_5851_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5839_, v___f_5850_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
if (lean_obj_tag(v___x_5851_) == 0)
{
return v___x_5851_;
}
else
{
lean_object* v_a_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5859_; 
v_a_5852_ = lean_ctor_get(v___x_5851_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5851_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5854_ = v___x_5851_;
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_a_5852_);
lean_dec(v___x_5851_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5857_; 
if (v_isShared_5855_ == 0)
{
v___x_5857_ = v___x_5854_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
v___x_5857_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
return v___x_5857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5860_, lean_object* v_x_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v_res_5871_; 
v_res_5871_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5860_, v_x_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
return v_res_5871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5872_, lean_object* v_mvarId_5873_, lean_object* v_x_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_){
_start:
{
lean_object* v___x_5884_; 
v___x_5884_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5873_, v_x_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5885_, lean_object* v_mvarId_5886_, lean_object* v_x_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
lean_object* v_res_5897_; 
v_res_5897_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5885_, v_mvarId_5886_, v_x_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
lean_dec(v___y_5895_);
lean_dec_ref(v___y_5894_);
lean_dec(v___y_5893_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
return v_res_5897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5898_, lean_object* v_pat_5899_, lean_object* v_a_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_){
_start:
{
lean_object* v___x_5910_; 
v___x_5910_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5898_, v_pat_5899_, v_a_5900_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
if (lean_obj_tag(v___x_5910_) == 0)
{
lean_object* v_a_5911_; lean_object* v___x_5912_; 
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_a_5911_);
lean_dec_ref_known(v___x_5910_, 1);
v___x_5912_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5911_, v___y_5902_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
return v___x_5912_;
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
v_a_5913_ = lean_ctor_get(v___x_5910_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5910_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5910_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5910_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5921_, lean_object* v_pat_5922_, lean_object* v_a_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_){
_start:
{
lean_object* v_res_5933_; 
v_res_5933_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5921_, v_pat_5922_, v_a_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_);
lean_dec(v___y_5931_);
lean_dec_ref(v___y_5930_);
lean_dec(v___y_5929_);
lean_dec_ref(v___y_5928_);
lean_dec(v___y_5927_);
lean_dec_ref(v___y_5926_);
lean_dec(v___y_5925_);
lean_dec_ref(v___y_5924_);
return v_res_5933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5934_, size_t v_i_5935_, lean_object* v_bs_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_){
_start:
{
uint8_t v___x_5941_; 
v___x_5941_ = lean_usize_dec_lt(v_i_5935_, v_sz_5934_);
if (v___x_5941_ == 0)
{
lean_object* v___x_5942_; 
v___x_5942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5942_, 0, v_bs_5936_);
return v___x_5942_;
}
else
{
lean_object* v_v_5943_; lean_object* v___x_5944_; lean_object* v_bs_x27_5945_; lean_object* v___x_5946_; 
v_v_5943_ = lean_array_uget(v_bs_5936_, v_i_5935_);
v___x_5944_ = lean_unsigned_to_nat(0u);
v_bs_x27_5945_ = lean_array_uset(v_bs_5936_, v_i_5935_, v___x_5944_);
v___x_5946_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_5943_, v___y_5937_, v___y_5938_, v___y_5939_);
if (lean_obj_tag(v___x_5946_) == 0)
{
lean_object* v_a_5947_; lean_object* v_hIdent_x3f_5948_; lean_object* v_term_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5960_; 
v_a_5947_ = lean_ctor_get(v___x_5946_, 0);
lean_inc(v_a_5947_);
lean_dec_ref_known(v___x_5946_, 1);
v_hIdent_x3f_5948_ = lean_ctor_get(v_a_5947_, 0);
v_term_5949_ = lean_ctor_get(v_a_5947_, 1);
v_isSharedCheck_5960_ = !lean_is_exclusive(v_a_5947_);
if (v_isSharedCheck_5960_ == 0)
{
v___x_5951_ = v_a_5947_;
v_isShared_5952_ = v_isSharedCheck_5960_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_term_5949_);
lean_inc(v_hIdent_x3f_5948_);
lean_dec(v_a_5947_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5960_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
lean_object* v___x_5954_; 
if (v_isShared_5952_ == 0)
{
v___x_5954_ = v___x_5951_;
goto v_reusejp_5953_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_hIdent_x3f_5948_);
lean_ctor_set(v_reuseFailAlloc_5959_, 1, v_term_5949_);
v___x_5954_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5953_;
}
v_reusejp_5953_:
{
size_t v___x_5955_; size_t v___x_5956_; lean_object* v___x_5957_; 
v___x_5955_ = ((size_t)1ULL);
v___x_5956_ = lean_usize_add(v_i_5935_, v___x_5955_);
v___x_5957_ = lean_array_uset(v_bs_x27_5945_, v_i_5935_, v___x_5954_);
v_i_5935_ = v___x_5956_;
v_bs_5936_ = v___x_5957_;
goto _start;
}
}
}
else
{
lean_object* v_a_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5968_; 
lean_dec_ref(v_bs_x27_5945_);
v_a_5961_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_5968_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_5968_ == 0)
{
v___x_5963_ = v___x_5946_;
v_isShared_5964_ = v_isSharedCheck_5968_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_a_5961_);
lean_dec(v___x_5946_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5968_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
lean_object* v___x_5966_; 
if (v_isShared_5964_ == 0)
{
v___x_5966_ = v___x_5963_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v_a_5961_);
v___x_5966_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
return v___x_5966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_5969_, lean_object* v_i_5970_, lean_object* v_bs_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_){
_start:
{
size_t v_sz_boxed_5976_; size_t v_i_boxed_5977_; lean_object* v_res_5978_; 
v_sz_boxed_5976_ = lean_unbox_usize(v_sz_5969_);
lean_dec(v_sz_5969_);
v_i_boxed_5977_ = lean_unbox_usize(v_i_5970_);
lean_dec(v_i_5970_);
v_res_5978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_5976_, v_i_boxed_5977_, v_bs_5971_, v___y_5972_, v___y_5973_, v___y_5974_);
lean_dec(v___y_5974_);
lean_dec_ref(v___y_5973_);
lean_dec_ref(v___y_5972_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_){
_start:
{
lean_object* v___y_5996_; lean_object* v_pat_5997_; lean_object* v___y_5998_; lean_object* v___y_5999_; lean_object* v___y_6000_; lean_object* v___y_6001_; lean_object* v___y_6002_; lean_object* v___y_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; lean_object* v___x_6031_; uint8_t v___x_6032_; 
v___x_6031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_5985_);
v___x_6032_ = l_Lean_Syntax_isOfKind(v_stx_5985_, v___x_6031_);
if (v___x_6032_ == 0)
{
lean_object* v___x_6033_; 
lean_dec(v_stx_5985_);
v___x_6033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6033_;
}
else
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; uint8_t v___x_6038_; 
v___x_6034_ = lean_unsigned_to_nat(1u);
v___x_6035_ = l_Lean_Syntax_getArg(v_stx_5985_, v___x_6034_);
v___x_6036_ = lean_unsigned_to_nat(2u);
v___x_6037_ = l_Lean_Syntax_getArg(v_stx_5985_, v___x_6036_);
v___x_6038_ = l_Lean_Syntax_isNone(v___x_6037_);
if (v___x_6038_ == 0)
{
uint8_t v___x_6039_; 
lean_dec(v_stx_5985_);
lean_inc(v___x_6037_);
v___x_6039_ = l_Lean_Syntax_matchesNull(v___x_6037_, v___x_6036_);
if (v___x_6039_ == 0)
{
lean_object* v___x_6040_; 
lean_dec(v___x_6037_);
lean_dec(v___x_6035_);
v___x_6040_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6040_;
}
else
{
lean_object* v_pat_x3f_6041_; lean_object* v_tgts_6042_; lean_object* v___x_6043_; 
v_pat_x3f_6041_ = l_Lean_Syntax_getArg(v___x_6037_, v___x_6034_);
lean_dec(v___x_6037_);
v_tgts_6042_ = l_Lean_Syntax_getArgs(v___x_6035_);
lean_dec(v___x_6035_);
v___x_6043_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6041_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
if (lean_obj_tag(v___x_6043_) == 0)
{
lean_object* v_a_6044_; 
v_a_6044_ = lean_ctor_get(v___x_6043_, 0);
lean_inc(v_a_6044_);
lean_dec_ref_known(v___x_6043_, 1);
v___y_5996_ = v_tgts_6042_;
v_pat_5997_ = v_a_6044_;
v___y_5998_ = v_a_5986_;
v___y_5999_ = v_a_5987_;
v___y_6000_ = v_a_5988_;
v___y_6001_ = v_a_5989_;
v___y_6002_ = v_a_5990_;
v___y_6003_ = v_a_5991_;
v___y_6004_ = v_a_5992_;
v___y_6005_ = v_a_5993_;
goto v___jp_5995_;
}
else
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6052_; 
lean_dec_ref(v_tgts_6042_);
v_a_6045_ = lean_ctor_get(v___x_6043_, 0);
v_isSharedCheck_6052_ = !lean_is_exclusive(v___x_6043_);
if (v_isSharedCheck_6052_ == 0)
{
v___x_6047_ = v___x_6043_;
v_isShared_6048_ = v_isSharedCheck_6052_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v___x_6043_);
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
else
{
lean_object* v___x_6053_; lean_object* v_tk_6054_; lean_object* v_tgts_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; 
lean_dec(v___x_6037_);
v___x_6053_ = lean_unsigned_to_nat(0u);
v_tk_6054_ = l_Lean_Syntax_getArg(v_stx_5985_, v___x_6053_);
lean_dec(v_stx_5985_);
v_tgts_6055_ = l_Lean_Syntax_getArgs(v___x_6035_);
lean_dec(v___x_6035_);
v___x_6056_ = lean_box(0);
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v_tk_6054_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___y_5996_ = v_tgts_6055_;
v_pat_5997_ = v___x_6057_;
v___y_5998_ = v_a_5986_;
v___y_5999_ = v_a_5987_;
v___y_6000_ = v_a_5988_;
v___y_6001_ = v_a_5989_;
v___y_6002_ = v_a_5990_;
v___y_6003_ = v_a_5991_;
v___y_6004_ = v_a_5992_;
v___y_6005_ = v_a_5993_;
goto v___jp_5995_;
}
}
v___jp_5995_:
{
lean_object* v___x_6006_; size_t v_sz_6007_; size_t v___x_6008_; lean_object* v___x_6009_; 
v___x_6006_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_5996_);
lean_dec_ref(v___y_5996_);
v_sz_6007_ = lean_array_size(v___x_6006_);
v___x_6008_ = ((size_t)0ULL);
v___x_6009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6007_, v___x_6008_, v___x_6006_, v___y_6002_, v___y_6004_, v___y_6005_);
if (lean_obj_tag(v___x_6009_) == 0)
{
lean_object* v_a_6010_; lean_object* v___x_6011_; 
v_a_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc(v_a_6010_);
lean_dec_ref_known(v___x_6009_, 1);
v___x_6011_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5999_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_);
if (lean_obj_tag(v___x_6011_) == 0)
{
lean_object* v_a_6012_; lean_object* v___f_6013_; lean_object* v___x_6014_; 
v_a_6012_ = lean_ctor_get(v___x_6011_, 0);
lean_inc_n(v_a_6012_, 2);
lean_dec_ref_known(v___x_6011_, 1);
v___f_6013_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6013_, 0, v_a_6010_);
lean_closure_set(v___f_6013_, 1, v_pat_5997_);
lean_closure_set(v___f_6013_, 2, v_a_6012_);
v___x_6014_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6012_, v___f_6013_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_);
return v___x_6014_;
}
else
{
lean_object* v_a_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6022_; 
lean_dec(v_a_6010_);
lean_dec_ref(v_pat_5997_);
v_a_6015_ = lean_ctor_get(v___x_6011_, 0);
v_isSharedCheck_6022_ = !lean_is_exclusive(v___x_6011_);
if (v_isSharedCheck_6022_ == 0)
{
v___x_6017_ = v___x_6011_;
v_isShared_6018_ = v_isSharedCheck_6022_;
goto v_resetjp_6016_;
}
else
{
lean_inc(v_a_6015_);
lean_dec(v___x_6011_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6022_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
lean_object* v___x_6020_; 
if (v_isShared_6018_ == 0)
{
v___x_6020_ = v___x_6017_;
goto v_reusejp_6019_;
}
else
{
lean_object* v_reuseFailAlloc_6021_; 
v_reuseFailAlloc_6021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6021_, 0, v_a_6015_);
v___x_6020_ = v_reuseFailAlloc_6021_;
goto v_reusejp_6019_;
}
v_reusejp_6019_:
{
return v___x_6020_;
}
}
}
}
else
{
lean_object* v_a_6023_; lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6030_; 
lean_dec_ref(v_pat_5997_);
v_a_6023_ = lean_ctor_get(v___x_6009_, 0);
v_isSharedCheck_6030_ = !lean_is_exclusive(v___x_6009_);
if (v_isSharedCheck_6030_ == 0)
{
v___x_6025_ = v___x_6009_;
v_isShared_6026_ = v_isSharedCheck_6030_;
goto v_resetjp_6024_;
}
else
{
lean_inc(v_a_6023_);
lean_dec(v___x_6009_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6030_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___x_6028_; 
if (v_isShared_6026_ == 0)
{
v___x_6028_ = v___x_6025_;
goto v_reusejp_6027_;
}
else
{
lean_object* v_reuseFailAlloc_6029_; 
v_reuseFailAlloc_6029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6029_, 0, v_a_6023_);
v___x_6028_ = v_reuseFailAlloc_6029_;
goto v_reusejp_6027_;
}
v_reusejp_6027_:
{
return v___x_6028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_){
_start:
{
lean_object* v_res_6068_; 
v_res_6068_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_);
lean_dec(v_a_6066_);
lean_dec_ref(v_a_6065_);
lean_dec(v_a_6064_);
lean_dec_ref(v_a_6063_);
lean_dec(v_a_6062_);
lean_dec_ref(v_a_6061_);
lean_dec(v_a_6060_);
lean_dec_ref(v_a_6059_);
return v_res_6068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6069_, size_t v_i_6070_, lean_object* v_bs_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v___x_6081_; 
v___x_6081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6069_, v_i_6070_, v_bs_6071_, v___y_6076_, v___y_6078_, v___y_6079_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6082_, lean_object* v_i_6083_, lean_object* v_bs_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
size_t v_sz_boxed_6094_; size_t v_i_boxed_6095_; lean_object* v_res_6096_; 
v_sz_boxed_6094_ = lean_unbox_usize(v_sz_6082_);
lean_dec(v_sz_6082_);
v_i_boxed_6095_ = lean_unbox_usize(v_i_6083_);
lean_dec(v_i_6083_);
v_res_6096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6094_, v_i_boxed_6095_, v_bs_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec(v___y_6086_);
lean_dec_ref(v___y_6085_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6133_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6136_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6137_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6133_, v___x_6134_, v___x_6135_, v___x_6136_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6140_, lean_object* v___x_6141_, lean_object* v_a_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
lean_object* v___x_6152_; 
v___x_6152_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6140_, v___x_6141_, v_a_6142_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
if (lean_obj_tag(v___x_6152_) == 0)
{
lean_object* v_a_6153_; lean_object* v___x_6154_; 
v_a_6153_ = lean_ctor_get(v___x_6152_, 0);
lean_inc(v_a_6153_);
lean_dec_ref_known(v___x_6152_, 1);
v___x_6154_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6153_, v___y_6144_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
return v___x_6154_;
}
else
{
lean_object* v_a_6155_; lean_object* v___x_6157_; uint8_t v_isShared_6158_; uint8_t v_isSharedCheck_6162_; 
v_a_6155_ = lean_ctor_get(v___x_6152_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6152_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6157_ = v___x_6152_;
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
else
{
lean_inc(v_a_6155_);
lean_dec(v___x_6152_);
v___x_6157_ = lean_box(0);
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
v_resetjp_6156_:
{
lean_object* v___x_6160_; 
if (v_isShared_6158_ == 0)
{
v___x_6160_ = v___x_6157_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6161_; 
v_reuseFailAlloc_6161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6161_, 0, v_a_6155_);
v___x_6160_ = v_reuseFailAlloc_6161_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
return v___x_6160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6163_, lean_object* v___x_6164_, lean_object* v_a_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6163_, v___x_6164_, v_a_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
lean_dec_ref(v___y_6168_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6176_, lean_object* v_val_6177_, lean_object* v_a_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v___x_6188_; 
v___x_6188_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6176_, v_val_6177_, v_a_6178_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_);
if (lean_obj_tag(v___x_6188_) == 0)
{
lean_object* v_a_6189_; lean_object* v___x_6190_; 
v_a_6189_ = lean_ctor_get(v___x_6188_, 0);
lean_inc(v_a_6189_);
lean_dec_ref_known(v___x_6188_, 1);
v___x_6190_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6189_, v___y_6180_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_);
return v___x_6190_;
}
else
{
lean_object* v_a_6191_; lean_object* v___x_6193_; uint8_t v_isShared_6194_; uint8_t v_isSharedCheck_6198_; 
v_a_6191_ = lean_ctor_get(v___x_6188_, 0);
v_isSharedCheck_6198_ = !lean_is_exclusive(v___x_6188_);
if (v_isSharedCheck_6198_ == 0)
{
v___x_6193_ = v___x_6188_;
v_isShared_6194_ = v_isSharedCheck_6198_;
goto v_resetjp_6192_;
}
else
{
lean_inc(v_a_6191_);
lean_dec(v___x_6188_);
v___x_6193_ = lean_box(0);
v_isShared_6194_ = v_isSharedCheck_6198_;
goto v_resetjp_6192_;
}
v_resetjp_6192_:
{
lean_object* v___x_6196_; 
if (v_isShared_6194_ == 0)
{
v___x_6196_ = v___x_6193_;
goto v_reusejp_6195_;
}
else
{
lean_object* v_reuseFailAlloc_6197_; 
v_reuseFailAlloc_6197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6197_, 0, v_a_6191_);
v___x_6196_ = v_reuseFailAlloc_6197_;
goto v_reusejp_6195_;
}
v_reusejp_6195_:
{
return v___x_6196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6199_, lean_object* v_val_6200_, lean_object* v_a_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_){
_start:
{
lean_object* v_res_6211_; 
v_res_6211_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6199_, v_val_6200_, v_a_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6204_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6202_);
return v_res_6211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_){
_start:
{
lean_object* v_ref_6218_; lean_object* v___x_6219_; lean_object* v_a_6220_; lean_object* v___x_6222_; uint8_t v_isShared_6223_; uint8_t v_isSharedCheck_6228_; 
v_ref_6218_ = lean_ctor_get(v___y_6215_, 2);
v___x_6219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_);
v_a_6220_ = lean_ctor_get(v___x_6219_, 0);
v_isSharedCheck_6228_ = !lean_is_exclusive(v___x_6219_);
if (v_isSharedCheck_6228_ == 0)
{
v___x_6222_ = v___x_6219_;
v_isShared_6223_ = v_isSharedCheck_6228_;
goto v_resetjp_6221_;
}
else
{
lean_inc(v_a_6220_);
lean_dec(v___x_6219_);
v___x_6222_ = lean_box(0);
v_isShared_6223_ = v_isSharedCheck_6228_;
goto v_resetjp_6221_;
}
v_resetjp_6221_:
{
lean_object* v___x_6224_; lean_object* v___x_6226_; 
lean_inc(v_ref_6218_);
v___x_6224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6224_, 0, v_ref_6218_);
lean_ctor_set(v___x_6224_, 1, v_a_6220_);
if (v_isShared_6223_ == 0)
{
lean_ctor_set_tag(v___x_6222_, 1);
lean_ctor_set(v___x_6222_, 0, v___x_6224_);
v___x_6226_ = v___x_6222_;
goto v_reusejp_6225_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v___x_6224_);
v___x_6226_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6225_;
}
v_reusejp_6225_:
{
return v___x_6226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
lean_dec(v___y_6233_);
lean_dec_ref(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6236_, size_t v_i_6237_, lean_object* v_bs_6238_){
_start:
{
uint8_t v___x_6239_; 
v___x_6239_ = lean_usize_dec_lt(v_i_6237_, v_sz_6236_);
if (v___x_6239_ == 0)
{
return v_bs_6238_;
}
else
{
lean_object* v_v_6240_; lean_object* v___x_6241_; lean_object* v_bs_x27_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; size_t v___x_6245_; size_t v___x_6246_; lean_object* v___x_6247_; 
v_v_6240_ = lean_array_uget(v_bs_6238_, v_i_6237_);
v___x_6241_ = lean_unsigned_to_nat(0u);
v_bs_x27_6242_ = lean_array_uset(v_bs_6238_, v_i_6237_, v___x_6241_);
v___x_6243_ = lean_box(0);
v___x_6244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6244_, 0, v___x_6243_);
lean_ctor_set(v___x_6244_, 1, v_v_6240_);
v___x_6245_ = ((size_t)1ULL);
v___x_6246_ = lean_usize_add(v_i_6237_, v___x_6245_);
v___x_6247_ = lean_array_uset(v_bs_x27_6242_, v_i_6237_, v___x_6244_);
v_i_6237_ = v___x_6246_;
v_bs_6238_ = v___x_6247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6249_, lean_object* v_i_6250_, lean_object* v_bs_6251_){
_start:
{
size_t v_sz_boxed_6252_; size_t v_i_boxed_6253_; lean_object* v_res_6254_; 
v_sz_boxed_6252_ = lean_unbox_usize(v_sz_6249_);
lean_dec(v_sz_6249_);
v_i_boxed_6253_ = lean_unbox_usize(v_i_6250_);
lean_dec(v_i_6250_);
v_res_6254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6252_, v_i_boxed_6253_, v_bs_6251_);
return v_res_6254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6266_ = l_Lean_stringToMessageData(v___x_6265_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6267_, lean_object* v_a_6268_, lean_object* v_a_6269_, lean_object* v_a_6270_, lean_object* v_a_6271_, lean_object* v_a_6272_, lean_object* v_a_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_){
_start:
{
lean_object* v___y_6278_; lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6287_; lean_object* v___x_6300_; uint8_t v___x_6301_; 
v___x_6300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6267_);
v___x_6301_ = l_Lean_Syntax_isOfKind(v_stx_6267_, v___x_6300_);
if (v___x_6301_ == 0)
{
lean_object* v___x_6302_; 
lean_dec(v_stx_6267_);
v___x_6302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6302_;
}
else
{
lean_object* v___x_6303_; lean_object* v_tk_6304_; lean_object* v___y_6306_; lean_object* v___y_6307_; lean_object* v___y_6308_; lean_object* v___y_6309_; lean_object* v___y_6310_; lean_object* v___y_6311_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6314_; lean_object* v___y_6315_; lean_object* v___y_6316_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v_a_6345_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v_val_x3f_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___x_6389_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v_ty_x3f_6393_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v_pat_x3f_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___x_6429_; uint8_t v___x_6430_; 
v___x_6303_ = lean_unsigned_to_nat(0u);
v_tk_6304_ = l_Lean_Syntax_getArg(v_stx_6267_, v___x_6303_);
v___x_6389_ = lean_unsigned_to_nat(1u);
v___x_6429_ = l_Lean_Syntax_getArg(v_stx_6267_, v___x_6389_);
v___x_6430_ = l_Lean_Syntax_isNone(v___x_6429_);
if (v___x_6430_ == 0)
{
uint8_t v___x_6431_; 
lean_inc(v___x_6429_);
v___x_6431_ = l_Lean_Syntax_matchesNull(v___x_6429_, v___x_6389_);
if (v___x_6431_ == 0)
{
lean_object* v___x_6432_; 
lean_dec(v___x_6429_);
lean_dec(v_tk_6304_);
lean_dec(v_stx_6267_);
v___x_6432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6432_;
}
else
{
lean_object* v_pat_x3f_6433_; lean_object* v___x_6434_; uint8_t v___x_6435_; 
v_pat_x3f_6433_ = l_Lean_Syntax_getArg(v___x_6429_, v___x_6303_);
lean_dec(v___x_6429_);
v___x_6434_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6433_);
v___x_6435_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6433_, v___x_6434_);
if (v___x_6435_ == 0)
{
lean_object* v___x_6436_; 
lean_dec(v_pat_x3f_6433_);
lean_dec(v_tk_6304_);
lean_dec(v_stx_6267_);
v___x_6436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6436_;
}
else
{
lean_object* v___x_6437_; 
v___x_6437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6437_, 0, v_pat_x3f_6433_);
v_pat_x3f_6412_ = v___x_6437_;
v___y_6413_ = v_a_6268_;
v___y_6414_ = v_a_6269_;
v___y_6415_ = v_a_6270_;
v___y_6416_ = v_a_6271_;
v___y_6417_ = v_a_6272_;
v___y_6418_ = v_a_6273_;
v___y_6419_ = v_a_6274_;
v___y_6420_ = v_a_6275_;
goto v___jp_6411_;
}
}
}
else
{
lean_object* v___x_6438_; 
lean_dec(v___x_6429_);
v___x_6438_ = lean_box(0);
v_pat_x3f_6412_ = v___x_6438_;
v___y_6413_ = v_a_6268_;
v___y_6414_ = v_a_6269_;
v___y_6415_ = v_a_6270_;
v___y_6416_ = v_a_6271_;
v___y_6417_ = v_a_6272_;
v___y_6418_ = v_a_6273_;
v___y_6419_ = v_a_6274_;
v___y_6420_ = v_a_6275_;
goto v___jp_6411_;
}
v___jp_6305_:
{
lean_object* v___x_6317_; lean_object* v___x_6318_; size_t v_sz_6319_; size_t v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6317_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6304_, v___y_6316_, v___y_6307_);
lean_dec(v___y_6307_);
v___x_6318_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6312_);
lean_dec_ref(v___y_6312_);
v_sz_6319_ = lean_array_size(v___x_6318_);
v___x_6320_ = ((size_t)0ULL);
v___x_6321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6319_, v___x_6320_, v___x_6318_);
v___x_6322_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6308_, v___y_6309_, v___y_6313_, v___y_6315_, v___y_6311_);
if (lean_obj_tag(v___x_6322_) == 0)
{
lean_object* v_a_6323_; lean_object* v___f_6324_; lean_object* v___x_6325_; 
v_a_6323_ = lean_ctor_get(v___x_6322_, 0);
lean_inc_n(v_a_6323_, 2);
lean_dec_ref_known(v___x_6322_, 1);
v___f_6324_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6324_, 0, v___x_6321_);
lean_closure_set(v___f_6324_, 1, v___x_6317_);
lean_closure_set(v___f_6324_, 2, v_a_6323_);
v___x_6325_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6323_, v___f_6324_, v___y_6306_, v___y_6308_, v___y_6310_, v___y_6314_, v___y_6309_, v___y_6313_, v___y_6315_, v___y_6311_);
return v___x_6325_;
}
else
{
lean_object* v_a_6326_; lean_object* v___x_6328_; uint8_t v_isShared_6329_; uint8_t v_isSharedCheck_6333_; 
lean_dec_ref(v___x_6321_);
lean_dec_ref(v___x_6317_);
v_a_6326_ = lean_ctor_get(v___x_6322_, 0);
v_isSharedCheck_6333_ = !lean_is_exclusive(v___x_6322_);
if (v_isSharedCheck_6333_ == 0)
{
v___x_6328_ = v___x_6322_;
v_isShared_6329_ = v_isSharedCheck_6333_;
goto v_resetjp_6327_;
}
else
{
lean_inc(v_a_6326_);
lean_dec(v___x_6322_);
v___x_6328_ = lean_box(0);
v_isShared_6329_ = v_isSharedCheck_6333_;
goto v_resetjp_6327_;
}
v_resetjp_6327_:
{
lean_object* v___x_6331_; 
if (v_isShared_6329_ == 0)
{
v___x_6331_ = v___x_6328_;
goto v_reusejp_6330_;
}
else
{
lean_object* v_reuseFailAlloc_6332_; 
v_reuseFailAlloc_6332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6332_, 0, v_a_6326_);
v___x_6331_ = v_reuseFailAlloc_6332_;
goto v_reusejp_6330_;
}
v_reusejp_6330_:
{
return v___x_6331_;
}
}
}
}
v___jp_6334_:
{
if (lean_obj_tag(v___y_6343_) == 1)
{
if (lean_obj_tag(v_a_6345_) == 0)
{
lean_object* v_val_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v_val_6346_ = lean_ctor_get(v___y_6343_, 0);
lean_inc(v_val_6346_);
lean_dec_ref_known(v___y_6343_, 1);
v___x_6347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6304_);
v___x_6348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6348_, 0, v_tk_6304_);
lean_ctor_set(v___x_6348_, 1, v___x_6347_);
v___y_6306_ = v___y_6336_;
v___y_6307_ = v___y_6335_;
v___y_6308_ = v___y_6337_;
v___y_6309_ = v___y_6338_;
v___y_6310_ = v___y_6340_;
v___y_6311_ = v___y_6339_;
v___y_6312_ = v_val_6346_;
v___y_6313_ = v___y_6341_;
v___y_6314_ = v___y_6342_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v___x_6348_;
goto v___jp_6305_;
}
else
{
lean_object* v_val_6349_; lean_object* v_val_6350_; 
v_val_6349_ = lean_ctor_get(v___y_6343_, 0);
lean_inc(v_val_6349_);
lean_dec_ref_known(v___y_6343_, 1);
v_val_6350_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_val_6350_);
lean_dec_ref_known(v_a_6345_, 1);
v___y_6306_ = v___y_6336_;
v___y_6307_ = v___y_6335_;
v___y_6308_ = v___y_6337_;
v___y_6309_ = v___y_6338_;
v___y_6310_ = v___y_6340_;
v___y_6311_ = v___y_6339_;
v___y_6312_ = v_val_6349_;
v___y_6313_ = v___y_6341_;
v___y_6314_ = v___y_6342_;
v___y_6315_ = v___y_6344_;
v___y_6316_ = v_val_6350_;
goto v___jp_6305_;
}
}
else
{
lean_dec(v___y_6343_);
if (lean_obj_tag(v___y_6335_) == 1)
{
if (lean_obj_tag(v_a_6345_) == 0)
{
lean_object* v_val_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; 
v_val_6351_ = lean_ctor_get(v___y_6335_, 0);
lean_inc(v_val_6351_);
lean_dec_ref_known(v___y_6335_, 1);
v___x_6352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6353_, 0, v_tk_6304_);
lean_ctor_set(v___x_6353_, 1, v___x_6352_);
v___y_6278_ = v_val_6351_;
v___y_6279_ = v___y_6336_;
v___y_6280_ = v___y_6337_;
v___y_6281_ = v___y_6338_;
v___y_6282_ = v___y_6340_;
v___y_6283_ = v___y_6339_;
v___y_6284_ = v___y_6341_;
v___y_6285_ = v___y_6342_;
v___y_6286_ = v___y_6344_;
v___y_6287_ = v___x_6353_;
goto v___jp_6277_;
}
else
{
lean_object* v_val_6354_; lean_object* v_val_6355_; 
lean_dec(v_tk_6304_);
v_val_6354_ = lean_ctor_get(v___y_6335_, 0);
lean_inc(v_val_6354_);
lean_dec_ref_known(v___y_6335_, 1);
v_val_6355_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_val_6355_);
lean_dec_ref_known(v_a_6345_, 1);
v___y_6278_ = v_val_6354_;
v___y_6279_ = v___y_6336_;
v___y_6280_ = v___y_6337_;
v___y_6281_ = v___y_6338_;
v___y_6282_ = v___y_6340_;
v___y_6283_ = v___y_6339_;
v___y_6284_ = v___y_6341_;
v___y_6285_ = v___y_6342_;
v___y_6286_ = v___y_6344_;
v___y_6287_ = v_val_6355_;
goto v___jp_6277_;
}
}
else
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
lean_dec(v_a_6345_);
lean_dec(v___y_6335_);
lean_dec(v_tk_6304_);
v___x_6356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6357_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6356_, v___y_6338_, v___y_6341_, v___y_6344_, v___y_6339_);
return v___x_6357_;
}
}
}
v___jp_6358_:
{
if (lean_obj_tag(v___y_6360_) == 0)
{
lean_object* v___x_6370_; 
v___x_6370_ = lean_box(0);
v___y_6335_ = v___y_6359_;
v___y_6336_ = v___y_6362_;
v___y_6337_ = v___y_6363_;
v___y_6338_ = v___y_6366_;
v___y_6339_ = v___y_6369_;
v___y_6340_ = v___y_6364_;
v___y_6341_ = v___y_6367_;
v___y_6342_ = v___y_6365_;
v___y_6343_ = v_val_x3f_6361_;
v___y_6344_ = v___y_6368_;
v_a_6345_ = v___x_6370_;
goto v___jp_6334_;
}
else
{
lean_object* v_val_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6388_; 
v_val_6371_ = lean_ctor_get(v___y_6360_, 0);
v_isSharedCheck_6388_ = !lean_is_exclusive(v___y_6360_);
if (v_isSharedCheck_6388_ == 0)
{
v___x_6373_ = v___y_6360_;
v_isShared_6374_ = v_isSharedCheck_6388_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_val_6371_);
lean_dec(v___y_6360_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6388_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v___x_6375_; 
v___x_6375_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6371_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_);
if (lean_obj_tag(v___x_6375_) == 0)
{
lean_object* v_a_6376_; lean_object* v___x_6378_; 
v_a_6376_ = lean_ctor_get(v___x_6375_, 0);
lean_inc(v_a_6376_);
lean_dec_ref_known(v___x_6375_, 1);
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 0, v_a_6376_);
v___x_6378_ = v___x_6373_;
goto v_reusejp_6377_;
}
else
{
lean_object* v_reuseFailAlloc_6379_; 
v_reuseFailAlloc_6379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_a_6376_);
v___x_6378_ = v_reuseFailAlloc_6379_;
goto v_reusejp_6377_;
}
v_reusejp_6377_:
{
v___y_6335_ = v___y_6359_;
v___y_6336_ = v___y_6362_;
v___y_6337_ = v___y_6363_;
v___y_6338_ = v___y_6366_;
v___y_6339_ = v___y_6369_;
v___y_6340_ = v___y_6364_;
v___y_6341_ = v___y_6367_;
v___y_6342_ = v___y_6365_;
v___y_6343_ = v_val_x3f_6361_;
v___y_6344_ = v___y_6368_;
v_a_6345_ = v___x_6378_;
goto v___jp_6334_;
}
}
else
{
lean_object* v_a_6380_; lean_object* v___x_6382_; uint8_t v_isShared_6383_; uint8_t v_isSharedCheck_6387_; 
lean_del_object(v___x_6373_);
lean_dec(v_val_x3f_6361_);
lean_dec(v___y_6359_);
lean_dec(v_tk_6304_);
v_a_6380_ = lean_ctor_get(v___x_6375_, 0);
v_isSharedCheck_6387_ = !lean_is_exclusive(v___x_6375_);
if (v_isSharedCheck_6387_ == 0)
{
v___x_6382_ = v___x_6375_;
v_isShared_6383_ = v_isSharedCheck_6387_;
goto v_resetjp_6381_;
}
else
{
lean_inc(v_a_6380_);
lean_dec(v___x_6375_);
v___x_6382_ = lean_box(0);
v_isShared_6383_ = v_isSharedCheck_6387_;
goto v_resetjp_6381_;
}
v_resetjp_6381_:
{
lean_object* v___x_6385_; 
if (v_isShared_6383_ == 0)
{
v___x_6385_ = v___x_6382_;
goto v_reusejp_6384_;
}
else
{
lean_object* v_reuseFailAlloc_6386_; 
v_reuseFailAlloc_6386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6386_, 0, v_a_6380_);
v___x_6385_ = v_reuseFailAlloc_6386_;
goto v_reusejp_6384_;
}
v_reusejp_6384_:
{
return v___x_6385_;
}
}
}
}
}
}
v___jp_6390_:
{
lean_object* v___x_6402_; lean_object* v___x_6403_; uint8_t v___x_6404_; 
v___x_6402_ = lean_unsigned_to_nat(3u);
v___x_6403_ = l_Lean_Syntax_getArg(v_stx_6267_, v___x_6402_);
lean_dec(v_stx_6267_);
v___x_6404_ = l_Lean_Syntax_isNone(v___x_6403_);
if (v___x_6404_ == 0)
{
uint8_t v___x_6405_; 
lean_inc(v___x_6403_);
v___x_6405_ = l_Lean_Syntax_matchesNull(v___x_6403_, v___y_6392_);
if (v___x_6405_ == 0)
{
lean_object* v___x_6406_; 
lean_dec(v___x_6403_);
lean_dec(v_ty_x3f_6393_);
lean_dec(v___y_6391_);
lean_dec(v_tk_6304_);
v___x_6406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6406_;
}
else
{
lean_object* v___x_6407_; lean_object* v_val_x3f_6408_; lean_object* v___x_6409_; 
v___x_6407_ = l_Lean_Syntax_getArg(v___x_6403_, v___x_6389_);
lean_dec(v___x_6403_);
v_val_x3f_6408_ = l_Lean_Syntax_getArgs(v___x_6407_);
lean_dec(v___x_6407_);
v___x_6409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6409_, 0, v_val_x3f_6408_);
v___y_6359_ = v_ty_x3f_6393_;
v___y_6360_ = v___y_6391_;
v_val_x3f_6361_ = v___x_6409_;
v___y_6362_ = v___y_6394_;
v___y_6363_ = v___y_6395_;
v___y_6364_ = v___y_6396_;
v___y_6365_ = v___y_6397_;
v___y_6366_ = v___y_6398_;
v___y_6367_ = v___y_6399_;
v___y_6368_ = v___y_6400_;
v___y_6369_ = v___y_6401_;
goto v___jp_6358_;
}
}
else
{
lean_object* v___x_6410_; 
lean_dec(v___x_6403_);
v___x_6410_ = lean_box(0);
v___y_6359_ = v_ty_x3f_6393_;
v___y_6360_ = v___y_6391_;
v_val_x3f_6361_ = v___x_6410_;
v___y_6362_ = v___y_6394_;
v___y_6363_ = v___y_6395_;
v___y_6364_ = v___y_6396_;
v___y_6365_ = v___y_6397_;
v___y_6366_ = v___y_6398_;
v___y_6367_ = v___y_6399_;
v___y_6368_ = v___y_6400_;
v___y_6369_ = v___y_6401_;
goto v___jp_6358_;
}
}
v___jp_6411_:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; uint8_t v___x_6423_; 
v___x_6421_ = lean_unsigned_to_nat(2u);
v___x_6422_ = l_Lean_Syntax_getArg(v_stx_6267_, v___x_6421_);
v___x_6423_ = l_Lean_Syntax_isNone(v___x_6422_);
if (v___x_6423_ == 0)
{
uint8_t v___x_6424_; 
lean_inc(v___x_6422_);
v___x_6424_ = l_Lean_Syntax_matchesNull(v___x_6422_, v___x_6421_);
if (v___x_6424_ == 0)
{
lean_object* v___x_6425_; 
lean_dec(v___x_6422_);
lean_dec(v_pat_x3f_6412_);
lean_dec(v_tk_6304_);
lean_dec(v_stx_6267_);
v___x_6425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6425_;
}
else
{
lean_object* v_ty_x3f_6426_; lean_object* v___x_6427_; 
v_ty_x3f_6426_ = l_Lean_Syntax_getArg(v___x_6422_, v___x_6389_);
lean_dec(v___x_6422_);
v___x_6427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6427_, 0, v_ty_x3f_6426_);
v___y_6391_ = v_pat_x3f_6412_;
v___y_6392_ = v___x_6421_;
v_ty_x3f_6393_ = v___x_6427_;
v___y_6394_ = v___y_6413_;
v___y_6395_ = v___y_6414_;
v___y_6396_ = v___y_6415_;
v___y_6397_ = v___y_6416_;
v___y_6398_ = v___y_6417_;
v___y_6399_ = v___y_6418_;
v___y_6400_ = v___y_6419_;
v___y_6401_ = v___y_6420_;
goto v___jp_6390_;
}
}
else
{
lean_object* v___x_6428_; 
lean_dec(v___x_6422_);
v___x_6428_ = lean_box(0);
v___y_6391_ = v_pat_x3f_6412_;
v___y_6392_ = v___x_6421_;
v_ty_x3f_6393_ = v___x_6428_;
v___y_6394_ = v___y_6413_;
v___y_6395_ = v___y_6414_;
v___y_6396_ = v___y_6415_;
v___y_6397_ = v___y_6416_;
v___y_6398_ = v___y_6417_;
v___y_6399_ = v___y_6418_;
v___y_6400_ = v___y_6419_;
v___y_6401_ = v___y_6420_;
goto v___jp_6390_;
}
}
}
v___jp_6277_:
{
lean_object* v___x_6288_; 
v___x_6288_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6280_, v___y_6281_, v___y_6284_, v___y_6286_, v___y_6283_);
if (lean_obj_tag(v___x_6288_) == 0)
{
lean_object* v_a_6289_; lean_object* v___f_6290_; lean_object* v___x_6291_; 
v_a_6289_ = lean_ctor_get(v___x_6288_, 0);
lean_inc_n(v_a_6289_, 2);
lean_dec_ref_known(v___x_6288_, 1);
v___f_6290_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6290_, 0, v___y_6287_);
lean_closure_set(v___f_6290_, 1, v___y_6278_);
lean_closure_set(v___f_6290_, 2, v_a_6289_);
v___x_6291_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6289_, v___f_6290_, v___y_6279_, v___y_6280_, v___y_6282_, v___y_6285_, v___y_6281_, v___y_6284_, v___y_6286_, v___y_6283_);
return v___x_6291_;
}
else
{
lean_object* v_a_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6299_; 
lean_dec_ref(v___y_6287_);
lean_dec(v___y_6278_);
v_a_6292_ = lean_ctor_get(v___x_6288_, 0);
v_isSharedCheck_6299_ = !lean_is_exclusive(v___x_6288_);
if (v_isSharedCheck_6299_ == 0)
{
v___x_6294_ = v___x_6288_;
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_a_6292_);
lean_dec(v___x_6288_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6297_; 
if (v_isShared_6295_ == 0)
{
v___x_6297_ = v___x_6294_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6298_; 
v_reuseFailAlloc_6298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6292_);
v___x_6297_ = v_reuseFailAlloc_6298_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
return v___x_6297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_, lean_object* v_a_6444_, lean_object* v_a_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_){
_start:
{
lean_object* v_res_6449_; 
v_res_6449_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6439_, v_a_6440_, v_a_6441_, v_a_6442_, v_a_6443_, v_a_6444_, v_a_6445_, v_a_6446_, v_a_6447_);
lean_dec(v_a_6447_);
lean_dec_ref(v_a_6446_);
lean_dec(v_a_6445_);
lean_dec_ref(v_a_6444_);
lean_dec(v_a_6443_);
lean_dec_ref(v_a_6442_);
lean_dec(v_a_6441_);
lean_dec_ref(v_a_6440_);
return v_res_6449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6450_, lean_object* v_msg_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_){
_start:
{
lean_object* v___x_6461_; 
v___x_6461_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6451_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_);
return v___x_6461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6462_, lean_object* v_msg_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_){
_start:
{
lean_object* v_res_6473_; 
v_res_6473_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6462_, v_msg_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_);
lean_dec(v___y_6471_);
lean_dec_ref(v___y_6470_);
lean_dec(v___y_6469_);
lean_dec_ref(v___y_6468_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
lean_dec(v___y_6465_);
lean_dec_ref(v___y_6464_);
return v_res_6473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
v___x_6479_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6482_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6483_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6479_, v___x_6480_, v___x_6481_, v___x_6482_);
return v___x_6483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6484_){
_start:
{
lean_object* v_res_6485_; 
v_res_6485_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6486_, lean_object* v_ty_x3f_6487_, lean_object* v_a_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_){
_start:
{
lean_object* v___x_6498_; 
v___x_6498_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6486_, v_ty_x3f_6487_, v_a_6488_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_);
if (lean_obj_tag(v___x_6498_) == 0)
{
lean_object* v_a_6499_; lean_object* v___x_6500_; 
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
lean_inc(v_a_6499_);
lean_dec_ref_known(v___x_6498_, 1);
v___x_6500_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6499_, v___y_6490_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_);
return v___x_6500_;
}
else
{
lean_object* v_a_6501_; lean_object* v___x_6503_; uint8_t v_isShared_6504_; uint8_t v_isSharedCheck_6508_; 
v_a_6501_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6508_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6508_ == 0)
{
v___x_6503_ = v___x_6498_;
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
else
{
lean_inc(v_a_6501_);
lean_dec(v___x_6498_);
v___x_6503_ = lean_box(0);
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
v_resetjp_6502_:
{
lean_object* v___x_6506_; 
if (v_isShared_6504_ == 0)
{
v___x_6506_ = v___x_6503_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6507_; 
v_reuseFailAlloc_6507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
v___x_6506_ = v_reuseFailAlloc_6507_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
return v___x_6506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6509_, lean_object* v_ty_x3f_6510_, lean_object* v_a_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_){
_start:
{
lean_object* v_res_6521_; 
v_res_6521_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6509_, v_ty_x3f_6510_, v_a_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_);
lean_dec(v___y_6519_);
lean_dec_ref(v___y_6518_);
lean_dec(v___y_6517_);
lean_dec_ref(v___y_6516_);
lean_dec(v___y_6515_);
lean_dec_ref(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6512_);
return v_res_6521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6528_, lean_object* v_a_6529_, lean_object* v_a_6530_, lean_object* v_a_6531_, lean_object* v_a_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_){
_start:
{
lean_object* v___x_6538_; uint8_t v___x_6539_; 
v___x_6538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6528_);
v___x_6539_ = l_Lean_Syntax_isOfKind(v_stx_6528_, v___x_6538_);
if (v___x_6539_ == 0)
{
lean_object* v___x_6540_; 
lean_dec(v_stx_6528_);
v___x_6540_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6540_;
}
else
{
lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v_ty_x3f_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___x_6566_; lean_object* v___x_6567_; uint8_t v___x_6568_; 
v___x_6541_ = lean_unsigned_to_nat(1u);
v___x_6542_ = l_Lean_Syntax_getArg(v_stx_6528_, v___x_6541_);
v___x_6566_ = lean_unsigned_to_nat(2u);
v___x_6567_ = l_Lean_Syntax_getArg(v_stx_6528_, v___x_6566_);
lean_dec(v_stx_6528_);
v___x_6568_ = l_Lean_Syntax_isNone(v___x_6567_);
if (v___x_6568_ == 0)
{
uint8_t v___x_6569_; 
lean_inc(v___x_6567_);
v___x_6569_ = l_Lean_Syntax_matchesNull(v___x_6567_, v___x_6566_);
if (v___x_6569_ == 0)
{
lean_object* v___x_6570_; 
lean_dec(v___x_6567_);
lean_dec(v___x_6542_);
v___x_6570_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6570_;
}
else
{
lean_object* v_ty_x3f_6571_; lean_object* v___x_6572_; 
v_ty_x3f_6571_ = l_Lean_Syntax_getArg(v___x_6567_, v___x_6541_);
lean_dec(v___x_6567_);
v___x_6572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6572_, 0, v_ty_x3f_6571_);
v_ty_x3f_6544_ = v___x_6572_;
v___y_6545_ = v_a_6529_;
v___y_6546_ = v_a_6530_;
v___y_6547_ = v_a_6531_;
v___y_6548_ = v_a_6532_;
v___y_6549_ = v_a_6533_;
v___y_6550_ = v_a_6534_;
v___y_6551_ = v_a_6535_;
v___y_6552_ = v_a_6536_;
goto v___jp_6543_;
}
}
else
{
lean_object* v___x_6573_; 
lean_dec(v___x_6567_);
v___x_6573_ = lean_box(0);
v_ty_x3f_6544_ = v___x_6573_;
v___y_6545_ = v_a_6529_;
v___y_6546_ = v_a_6530_;
v___y_6547_ = v_a_6531_;
v___y_6548_ = v_a_6532_;
v___y_6549_ = v_a_6533_;
v___y_6550_ = v_a_6534_;
v___y_6551_ = v_a_6535_;
v___y_6552_ = v_a_6536_;
goto v___jp_6543_;
}
v___jp_6543_:
{
lean_object* v_pats_6553_; lean_object* v___x_6554_; 
v_pats_6553_ = l_Lean_Syntax_getArgs(v___x_6542_);
lean_dec(v___x_6542_);
v___x_6554_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6546_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_);
if (lean_obj_tag(v___x_6554_) == 0)
{
lean_object* v_a_6555_; lean_object* v___f_6556_; lean_object* v___x_6557_; 
v_a_6555_ = lean_ctor_get(v___x_6554_, 0);
lean_inc_n(v_a_6555_, 2);
lean_dec_ref_known(v___x_6554_, 1);
v___f_6556_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6556_, 0, v_pats_6553_);
lean_closure_set(v___f_6556_, 1, v_ty_x3f_6544_);
lean_closure_set(v___f_6556_, 2, v_a_6555_);
v___x_6557_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6555_, v___f_6556_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_);
return v___x_6557_;
}
else
{
lean_object* v_a_6558_; lean_object* v___x_6560_; uint8_t v_isShared_6561_; uint8_t v_isSharedCheck_6565_; 
lean_dec_ref(v_pats_6553_);
lean_dec(v_ty_x3f_6544_);
v_a_6558_ = lean_ctor_get(v___x_6554_, 0);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6554_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6560_ = v___x_6554_;
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
else
{
lean_inc(v_a_6558_);
lean_dec(v___x_6554_);
v___x_6560_ = lean_box(0);
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
v_resetjp_6559_:
{
lean_object* v___x_6563_; 
if (v_isShared_6561_ == 0)
{
v___x_6563_ = v___x_6560_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v_a_6558_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
return v___x_6563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_, lean_object* v_a_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v_res_6584_; 
v_res_6584_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6574_, v_a_6575_, v_a_6576_, v_a_6577_, v_a_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
lean_dec(v_a_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_a_6580_);
lean_dec_ref(v_a_6579_);
lean_dec(v_a_6578_);
lean_dec_ref(v_a_6577_);
lean_dec(v_a_6576_);
lean_dec_ref(v_a_6575_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; 
v___x_6590_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6593_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6594_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6590_, v___x_6591_, v___x_6592_, v___x_6593_);
return v___x_6594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6595_){
_start:
{
lean_object* v_res_6596_; 
v_res_6596_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6596_;
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
