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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_mkTargetView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.RCases"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Elab.Tactic.RCases.0.Lean.Elab.Tactic.RCases.rcasesCore"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0;
static const lean_array_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` is not an inductive datatype"};
static const lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_104_ = l_Array_mkArray0(lean_box(0));
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
v___x_969_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_1013_; lean_object* v_env_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_st_ref_get(v___y_1011_);
v_env_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_env_1014_);
lean_dec(v___x_1013_);
v___x_1015_ = l_Lean_Name_isAnonymous(v_declHint_1010_);
if (v___x_1015_ == 0)
{
uint8_t v_isExporting_1016_; 
v_isExporting_1016_ = lean_ctor_get_uint8(v_env_1014_, sizeof(void*)*8);
if (v_isExporting_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_msg_1009_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
lean_inc_ref(v_env_1014_);
v___x_1018_ = l_Lean_Environment_setExporting(v_env_1014_, v___x_1015_);
lean_inc(v_declHint_1010_);
lean_inc_ref(v___x_1018_);
v___x_1019_ = l_Lean_Environment_contains(v___x_1018_, v_declHint_1010_, v_isExporting_1016_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v___x_1018_);
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_1009_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_c_1026_; lean_object* v___x_1027_; 
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1022_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1023_ = l_Lean_Options_empty;
v___x_1024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1018_);
lean_ctor_set(v___x_1024_, 1, v___x_1021_);
lean_ctor_set(v___x_1024_, 2, v___x_1022_);
lean_ctor_set(v___x_1024_, 3, v___x_1023_);
lean_inc(v_declHint_1010_);
v___x_1025_ = l_Lean_MessageData_ofConstName(v_declHint_1010_, v___x_1015_);
v_c_1026_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1026_, 0, v___x_1024_);
lean_ctor_set(v_c_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1014_, v_declHint_1010_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_c_1026_);
v___x_1030_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_MessageData_note(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_msg_1009_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1070_; 
v_val_1035_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1037_ = v___x_1027_;
v_isShared_1038_ = v_isSharedCheck_1070_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v___x_1027_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1070_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_mod_1042_; uint8_t v___x_1043_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_Environment_header(v_env_1014_);
lean_dec_ref(v_env_1014_);
v___x_1041_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1040_);
v_mod_1042_ = lean_array_get(v___x_1039_, v___x_1041_, v_val_1035_);
lean_dec(v_val_1035_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Lean_isPrivateName(v_declHint_1010_);
lean_dec(v_declHint_1010_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1026_);
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
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1053_);
v___x_1055_ = v___x_1037_;
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
lean_ctor_set(v___x_1058_, 1, v_c_1026_);
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
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1066_);
v___x_1068_ = v___x_1037_;
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
lean_dec_ref(v_env_1014_);
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
lean_object* v_toCold_1157_; lean_object* v_currRecDepth_1158_; lean_object* v_ref_1159_; uint8_t v_diag_1160_; uint8_t v_suppressElabErrors_1161_; lean_object* v_ref_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_toCold_1157_ = lean_ctor_get(v___y_1154_, 0);
v_currRecDepth_1158_ = lean_ctor_get(v___y_1154_, 1);
v_ref_1159_ = lean_ctor_get(v___y_1154_, 2);
v_diag_1160_ = lean_ctor_get_uint8(v___y_1154_, sizeof(void*)*3);
v_suppressElabErrors_1161_ = lean_ctor_get_uint8(v___y_1154_, sizeof(void*)*3 + 1);
v_ref_1162_ = l_Lean_replaceRef(v_ref_1150_, v_ref_1159_);
lean_inc(v_currRecDepth_1158_);
lean_inc_ref(v_toCold_1157_);
v___x_1163_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1163_, 0, v_toCold_1157_);
lean_ctor_set(v___x_1163_, 1, v_currRecDepth_1158_);
lean_ctor_set(v___x_1163_, 2, v_ref_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3, v_diag_1160_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*3 + 1, v_suppressElabErrors_1161_);
v___x_1164_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1151_, v___y_1152_, v___y_1153_, v___x_1163_, v___y_1155_);
lean_dec_ref_known(v___x_1163_, 3);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1165_, v_msg_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v_ref_1165_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1173_, lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1183_; 
v___x_1181_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1174_, v_declHint_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1173_, v_a_1182_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1184_, lean_object* v_msg_1185_, lean_object* v_declHint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1184_, v_msg_1185_, v_declHint_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v_ref_1184_);
return v_res_1192_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1199_, lean_object* v_constName_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1206_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1207_ = 0;
lean_inc(v_constName_1200_);
v___x_1208_ = l_Lean_MessageData_ofConstName(v_constName_1200_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1199_, v___x_1211_, v_constName_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1213_, lean_object* v_constName_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1213_, v_constName_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_ref_1213_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_ref_1227_; lean_object* v___x_1228_; 
v_ref_1227_ = lean_ctor_get(v___y_1224_, 2);
v___x_1228_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1227_, v_constName_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object* v_constName_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; lean_object* v_env_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_st_ref_get(v___y_1240_);
v_env_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_env_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = 0;
lean_inc(v_constName_1236_);
v___x_1245_ = l_Lean_Environment_findConstVal_x3f(v_env_1243_, v_constName_1236_, v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1246_;
}
else
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_constName_1236_);
v_val_1247_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1245_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v___x_1245_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 0);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_val_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object* v_constName_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l_List_reverse___redArg(v_a_1263_);
return v___x_1264_;
}
else
{
lean_object* v_head_1265_; lean_object* v_tail_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1275_; 
v_head_1265_ = lean_ctor_get(v_a_1262_, 0);
v_tail_1266_ = lean_ctor_get(v_a_1262_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1268_ = v_a_1262_;
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_tail_1266_);
lean_inc(v_head_1265_);
lean_dec(v_a_1262_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = l_Lean_mkLevelParam(v_head_1265_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_a_1263_);
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_a_1263_);
v___x_1272_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v_a_1262_ = v_tail_1266_;
v_a_1263_ = v___x_1272_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object* v_constName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
lean_inc(v_constName_1276_);
v___x_1282_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1294_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_levelParams_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_levelParams_1287_ = lean_ctor_get(v_a_1283_, 1);
lean_inc(v_levelParams_1287_);
lean_dec(v_a_1283_);
v___x_1288_ = lean_box(0);
v___x_1289_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(v_levelParams_1287_, v___x_1288_);
v___x_1290_ = l_Lean_mkConst(v_constName_1276_, v___x_1289_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1290_);
v___x_1292_ = v___x_1285_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_constName_1276_);
v_a_1295_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1282_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1282_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object* v_constName_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_constName_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object* v_ref_1310_, lean_object* v_params_1311_, lean_object* v_altVarNames_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_x_1314_);
lean_dec(v_ref_1310_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_altVarNames_1312_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
else
{
lean_object* v_head_1323_; lean_object* v_tail_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1430_; 
v_head_1323_ = lean_ctor_get(v_x_1313_, 0);
v_tail_1324_ = lean_ctor_get(v_x_1313_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_x_1313_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1326_ = v_x_1313_;
v_isShared_1327_ = v_isSharedCheck_1430_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_tail_1324_);
lean_inc(v_head_1323_);
lean_dec(v_x_1313_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1430_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; 
lean_inc(v_head_1323_);
v___x_1328_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_head_1323_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Lean_Meta_getFunInfo(v_a_1329_, v___x_1330_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v_paramInfo_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1412_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v_paramInfo_1333_ = lean_ctor_get(v_a_1332_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1332_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_a_1332_, 1);
lean_dec(v_unused_1413_);
v___x_1335_ = v_a_1332_;
v_isShared_1336_ = v_isSharedCheck_1412_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_paramInfo_1333_);
lean_dec(v_a_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1412_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___y_1338_; lean_object* v___y_1339_; uint8_t v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1377_; uint8_t v_fst_1378_; lean_object* v_snd_1379_; lean_object* v_snd_1380_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1407_; 
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v___x_1410_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_1407_ = v___x_1410_;
goto v___jp_1406_;
}
else
{
lean_object* v_head_1411_; 
v_head_1411_ = lean_ctor_get(v_x_1314_, 0);
lean_inc(v_head_1411_);
v___y_1407_ = v_head_1411_;
goto v___jp_1406_;
}
v___jp_1337_:
{
lean_object* v___x_1342_; lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1375_; 
v___x_1342_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1341_, v_paramInfo_1333_, v___y_1340_, v_params_1311_, v___y_1339_);
lean_dec_ref(v_paramInfo_1333_);
v_fst_1343_ = lean_ctor_get(v___x_1342_, 0);
v_snd_1344_ = lean_ctor_get(v___x_1342_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1346_ = v___x_1342_;
v_isShared_1347_ = v_isSharedCheck_1375_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v___x_1342_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1375_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = 1;
v___x_1349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1349_, 0, v_fst_1343_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1348_);
v___x_1350_ = lean_array_push(v_altVarNames_1312_, v___x_1349_);
v___x_1351_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1310_, v_params_1311_, v___x_1350_, v_tail_1324_, v___y_1338_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1374_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1374_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1374_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1373_; 
v_fst_1356_ = lean_ctor_get(v_a_1352_, 0);
v_snd_1357_ = lean_ctor_get(v_a_1352_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1352_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1359_ = v_a_1352_;
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_inc(v_fst_1356_);
lean_dec(v_a_1352_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_snd_1344_);
lean_ctor_set(v___x_1359_, 0, v_head_1323_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_head_1323_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_snd_1344_);
v___x_1362_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_snd_1357_);
lean_ctor_set(v___x_1326_, 0, v___x_1362_);
v___x_1364_ = v___x_1326_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_snd_1357_);
v___x_1364_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1364_);
lean_ctor_set(v___x_1346_, 0, v_fst_1356_);
v___x_1366_ = v___x_1346_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_fst_1356_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1366_);
v___x_1368_ = v___x_1354_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_del_object(v___x_1326_);
lean_dec(v_head_1323_);
return v___x_1351_;
}
}
}
v___jp_1376_:
{
lean_object* v_ref_1381_; 
v_ref_1381_ = lean_ctor_get(v___y_1377_, 0);
lean_inc(v_ref_1381_);
lean_dec_ref(v___y_1377_);
v___y_1338_ = v_snd_1380_;
v___y_1339_ = v_snd_1379_;
v___y_1340_ = v_fst_1378_;
v___y_1341_ = v_ref_1381_;
goto v___jp_1337_;
}
v___jp_1382_:
{
lean_object* v___x_1385_; lean_object* v_fst_1386_; lean_object* v_snd_1387_; uint8_t v___x_1388_; 
lean_inc_ref(v___y_1384_);
v___x_1385_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1384_);
v_fst_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_fst_1386_);
v_snd_1387_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_snd_1387_);
lean_dec_ref(v___x_1385_);
v___x_1388_ = lean_unbox(v_fst_1386_);
lean_dec(v_fst_1386_);
v___y_1377_ = v___y_1384_;
v_fst_1378_ = v___x_1388_;
v_snd_1379_ = v_snd_1387_;
v_snd_1380_ = v___y_1383_;
goto v___jp_1376_;
}
v___jp_1389_:
{
if (lean_obj_tag(v_tail_1324_) == 0)
{
if (lean_obj_tag(v___y_1392_) == 1)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
v_isSharedCheck_1403_ = !lean_is_exclusive(v___y_1392_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1404_ = lean_ctor_get(v___y_1392_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v___y_1392_, 0);
lean_dec(v_unused_1405_);
v___x_1394_ = v___y_1392_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v___y_1392_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
uint8_t v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = 0;
lean_inc(v_ref_1310_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 6);
lean_ctor_set(v___x_1335_, 1, v_x_1314_);
lean_ctor_set(v___x_1335_, 0, v_ref_1310_);
v___x_1398_ = v___x_1335_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_ref_1310_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_x_1314_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___y_1390_);
lean_ctor_set(v___x_1394_, 0, v___x_1398_);
v___x_1400_ = v___x_1394_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___y_1390_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v___y_1377_ = v___y_1391_;
v_fst_1378_ = v___x_1396_;
v_snd_1379_ = v___x_1400_;
v_snd_1380_ = v___y_1390_;
goto v___jp_1376_;
}
}
}
}
else
{
lean_dec(v___y_1390_);
lean_del_object(v___x_1335_);
lean_dec(v_x_1314_);
v___y_1383_ = v___y_1392_;
v___y_1384_ = v___y_1391_;
goto v___jp_1382_;
}
}
else
{
lean_dec(v___y_1390_);
lean_del_object(v___x_1335_);
lean_dec(v_x_1314_);
v___y_1383_ = v___y_1392_;
v___y_1384_ = v___y_1391_;
goto v___jp_1382_;
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_box(0);
if (lean_obj_tag(v_x_1314_) == 0)
{
v___y_1390_ = v___x_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___x_1408_;
goto v___jp_1389_;
}
else
{
lean_object* v_tail_1409_; 
v_tail_1409_ = lean_ctor_get(v_x_1314_, 1);
lean_inc(v_tail_1409_);
v___y_1390_ = v___x_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v_tail_1409_;
goto v___jp_1389_;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_del_object(v___x_1326_);
lean_dec(v_tail_1324_);
lean_dec(v_head_1323_);
lean_dec(v_x_1314_);
lean_dec_ref(v_altVarNames_1312_);
lean_dec(v_ref_1310_);
v_a_1414_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1331_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1331_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_del_object(v___x_1326_);
lean_dec(v_tail_1324_);
lean_dec(v_head_1323_);
lean_dec(v_x_1314_);
lean_dec_ref(v_altVarNames_1312_);
lean_dec(v_ref_1310_);
v_a_1422_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1328_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1328_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object* v_ref_1431_, lean_object* v_params_1432_, lean_object* v_altVarNames_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1431_, v_params_1432_, v_altVarNames_1433_, v_x_1434_, v_x_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_params_1432_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1442_, lean_object* v_constName_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_constName_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(v_00_u03b1_1450_, v_constName_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1458_, lean_object* v_ref_1459_, lean_object* v_constName_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1459_, v_constName_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1467_, lean_object* v_ref_1468_, lean_object* v_constName_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1467_, v_ref_1468_, v_constName_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_ref_1468_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1476_, lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v_declHint_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1477_, v_msg_1478_, v_declHint_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_ref_1487_, lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1486_, v_ref_1487_, v_msg_1488_, v_declHint_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_ref_1487_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1496_, v_declHint_1497_, v___y_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1504_, lean_object* v_declHint_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(v_msg_1504_, v_declHint_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1512_, lean_object* v_ref_1513_, lean_object* v_msg_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1513_, v_msg_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_ref_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1521_, v_ref_1522_, v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v_ref_1522_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1538_, lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1538_, v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object* v_e_1546_, lean_object* v_cont_1547_, lean_object* v_g_1548_, lean_object* v_fs_1549_, lean_object* v_clears_1550_, lean_object* v_a_1551_, lean_object* v_ref_1552_, lean_object* v_a_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_Expr_isFVar(v_e_1546_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec(v_ref_1552_);
lean_dec_ref(v_e_1546_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
v___x_1562_ = lean_apply_11(v_cont_1547_, v_g_1548_, v_fs_1549_, v_clears_1550_, v_a_1551_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, lean_box(0));
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_1552_, v_e_1546_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref_known(v___x_1563_, 1);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
v___x_1564_ = lean_apply_11(v_cont_1547_, v_g_1548_, v_fs_1549_, v_clears_1550_, v_a_1551_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, lean_box(0));
return v___x_1564_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1551_);
lean_dec_ref(v_clears_1550_);
lean_dec(v_fs_1549_);
lean_dec(v_g_1548_);
lean_dec_ref(v_cont_1547_);
v_a_1565_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1563_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object* v_e_1573_, lean_object* v_cont_1574_, lean_object* v_g_1575_, lean_object* v_fs_1576_, lean_object* v_clears_1577_, lean_object* v_a_1578_, lean_object* v_ref_1579_, lean_object* v_a_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(v_e_1573_, v_cont_1574_, v_g_1575_, v_fs_1576_, v_clears_1577_, v_a_1578_, v_ref_1579_, v_a_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v_a_1580_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
v___x_1597_ = lean_apply_7(v_x_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, lean_box(0));
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object* v_x_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(v_x_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object* v_mvarId_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___f_1616_; lean_object* v___x_1617_; 
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1616_, 0, v_x_1608_);
lean_closure_set(v___f_1616_, 1, v___y_1609_);
lean_closure_set(v___f_1616_, 2, v___y_1610_);
v___x_1617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1607_, v___f_1616_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1617_) == 0)
{
return v___x_1617_;
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object* v_mvarId_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_1626_, v_x_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1635_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object* v_x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 1)
{
lean_object* v_fvarId_1648_; lean_object* v___x_1649_; 
v_fvarId_1648_ = lean_ctor_get(v_x_1642_, 0);
lean_inc(v_fvarId_1648_);
lean_dec_ref_known(v_x_1642_, 1);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_fvarId_1648_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1651_ = l_Lean_MessageData_ofExpr(v_x_1642_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v___x_1654_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object* v_x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(v_x_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_ks_1667_; lean_object* v_vs_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1692_; 
v_ks_1667_ = lean_ctor_get(v_x_1663_, 0);
v_vs_1668_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1670_ = v_x_1663_;
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_vs_1668_);
lean_inc(v_ks_1667_);
lean_dec(v_x_1663_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = lean_array_get_size(v_ks_1667_);
v___x_1673_ = lean_nat_dec_lt(v_x_1664_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec(v_x_1664_);
v___x_1674_ = lean_array_push(v_ks_1667_, v_x_1665_);
v___x_1675_ = lean_array_push(v_vs_1668_, v_x_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1675_);
lean_ctor_set(v___x_1670_, 0, v___x_1674_);
v___x_1677_ = v___x_1670_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
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
lean_object* v_k_x27_1679_; uint8_t v___x_1680_; 
v_k_x27_1679_ = lean_array_fget_borrowed(v_ks_1667_, v_x_1664_);
v___x_1680_ = l_Lean_instBEqMVarId_beq(v_x_1665_, v_k_x27_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1682_; 
if (v_isShared_1671_ == 0)
{
v___x_1682_ = v___x_1670_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_ks_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_vs_1668_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_x_1664_, v___x_1683_);
lean_dec(v_x_1664_);
v_x_1663_ = v___x_1682_;
v_x_1664_ = v___x_1684_;
goto _start;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1687_ = lean_array_fset(v_ks_1667_, v_x_1664_, v_x_1665_);
v___x_1688_ = lean_array_fset(v_vs_1668_, v_x_1664_, v_x_1666_);
lean_dec(v_x_1664_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1688_);
lean_ctor_set(v___x_1670_, 0, v___x_1687_);
v___x_1690_ = v___x_1670_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object* v_n_1693_, lean_object* v_k_1694_, lean_object* v_v_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_n_1693_, v___x_1696_, v_k_1694_, v_v_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object* v_x_1699_, size_t v_x_1700_, size_t v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_es_1704_; size_t v___x_1705_; size_t v___x_1706_; lean_object* v_j_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_es_1704_ = lean_ctor_get(v_x_1699_, 0);
v___x_1705_ = ((size_t)31ULL);
v___x_1706_ = lean_usize_land(v_x_1700_, v___x_1705_);
v_j_1707_ = lean_usize_to_nat(v___x_1706_);
v___x_1708_ = lean_array_get_size(v_es_1704_);
v___x_1709_ = lean_nat_dec_lt(v_j_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v_j_1707_);
lean_dec(v_x_1703_);
lean_dec(v_x_1702_);
return v_x_1699_;
}
else
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1748_; 
lean_inc_ref(v_es_1704_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v_x_1699_, 0);
lean_dec(v_unused_1749_);
v___x_1711_ = v_x_1699_;
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v_x_1699_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1748_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_v_1713_; lean_object* v___x_1714_; lean_object* v_xs_x27_1715_; lean_object* v___y_1717_; 
v_v_1713_ = lean_array_fget(v_es_1704_, v_j_1707_);
v___x_1714_ = lean_box(0);
v_xs_x27_1715_ = lean_array_fset(v_es_1704_, v_j_1707_, v___x_1714_);
switch(lean_obj_tag(v_v_1713_))
{
case 0:
{
lean_object* v_key_1722_; lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1733_; 
v_key_1722_ = lean_ctor_get(v_v_1713_, 0);
v_val_1723_ = lean_ctor_get(v_v_1713_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_v_1713_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1725_ = v_v_1713_;
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_inc(v_key_1722_);
lean_dec(v_v_1713_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1733_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = l_Lean_instBEqMVarId_beq(v_x_1702_, v_key_1722_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1725_);
v___x_1728_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1722_, v_val_1723_, v_x_1702_, v_x_1703_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___y_1717_ = v___x_1729_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_val_1723_);
lean_dec(v_key_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_x_1703_);
lean_ctor_set(v___x_1725_, 0, v_x_1702_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1702_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_x_1703_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v___y_1717_ = v___x_1731_;
goto v___jp_1716_;
}
}
}
}
case 1:
{
lean_object* v_node_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1746_; 
v_node_1734_ = lean_ctor_get(v_v_1713_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_v_1713_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1736_ = v_v_1713_;
v_isShared_1737_ = v_isSharedCheck_1746_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_node_1734_);
lean_dec(v_v_1713_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1746_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_usize_shift_right(v_x_1700_, v___x_1738_);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_x_1701_, v___x_1740_);
v___x_1742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_node_1734_, v___x_1739_, v___x_1741_, v_x_1702_, v_x_1703_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1742_);
v___x_1744_ = v___x_1736_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v___y_1717_ = v___x_1744_;
goto v___jp_1716_;
}
}
}
default: 
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_x_1702_);
lean_ctor_set(v___x_1747_, 1, v_x_1703_);
v___y_1717_ = v___x_1747_;
goto v___jp_1716_;
}
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_array_fset(v_xs_x27_1715_, v_j_1707_, v___y_1717_);
lean_dec(v_j_1707_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1718_);
v___x_1720_ = v___x_1711_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v_ks_1750_; lean_object* v_vs_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1769_; 
v_ks_1750_ = lean_ctor_get(v_x_1699_, 0);
v_vs_1751_ = lean_ctor_get(v_x_1699_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_x_1699_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1753_ = v_x_1699_;
v_isShared_1754_ = v_isSharedCheck_1769_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_vs_1751_);
lean_inc(v_ks_1750_);
lean_dec(v_x_1699_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1769_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_ks_1750_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_vs_1751_);
v___x_1756_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v_newNode_1757_; size_t v___x_1758_; uint8_t v___x_1759_; 
v_newNode_1757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1756_, v_x_1702_, v_x_1703_);
v___x_1758_ = ((size_t)7ULL);
v___x_1759_ = lean_usize_dec_le(v___x_1758_, v_x_1701_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1757_);
v___x_1761_ = lean_unsigned_to_nat(4u);
v___x_1762_ = lean_nat_dec_lt(v___x_1760_, v___x_1761_);
lean_dec(v___x_1760_);
if (v___x_1762_ == 0)
{
lean_object* v_ks_1763_; lean_object* v_vs_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_ks_1763_ = lean_ctor_get(v_newNode_1757_, 0);
lean_inc_ref(v_ks_1763_);
v_vs_1764_ = lean_ctor_get(v_newNode_1757_, 1);
lean_inc_ref(v_vs_1764_);
lean_dec_ref(v_newNode_1757_);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1701_, v_ks_1763_, v_vs_1764_, v___x_1765_, v___x_1766_);
lean_dec_ref(v_vs_1764_);
lean_dec_ref(v_ks_1763_);
return v___x_1767_;
}
else
{
return v_newNode_1757_;
}
}
else
{
return v_newNode_1757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1770_, lean_object* v_keys_1771_, lean_object* v_vals_1772_, lean_object* v_i_1773_, lean_object* v_entries_1774_){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_array_get_size(v_keys_1771_);
v___x_1776_ = lean_nat_dec_lt(v_i_1773_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v_i_1773_);
return v_entries_1774_;
}
else
{
lean_object* v_k_1777_; lean_object* v_v_1778_; uint64_t v___x_1779_; size_t v_h_1780_; size_t v___x_1781_; lean_object* v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; size_t v___x_1785_; size_t v_h_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_k_1777_ = lean_array_fget_borrowed(v_keys_1771_, v_i_1773_);
v_v_1778_ = lean_array_fget_borrowed(v_vals_1772_, v_i_1773_);
v___x_1779_ = l_Lean_instHashableMVarId_hash(v_k_1777_);
v_h_1780_ = lean_uint64_to_usize(v___x_1779_);
v___x_1781_ = ((size_t)5ULL);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_sub(v_depth_1770_, v___x_1783_);
v___x_1785_ = lean_usize_mul(v___x_1781_, v___x_1784_);
v_h_1786_ = lean_usize_shift_right(v_h_1780_, v___x_1785_);
v___x_1787_ = lean_nat_add(v_i_1773_, v___x_1782_);
lean_dec(v_i_1773_);
lean_inc(v_v_1778_);
lean_inc(v_k_1777_);
v___x_1788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1774_, v_h_1786_, v_depth_1770_, v_k_1777_, v_v_1778_);
v_i_1773_ = v___x_1787_;
v_entries_1774_ = v___x_1788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1790_, lean_object* v_keys_1791_, lean_object* v_vals_1792_, lean_object* v_i_1793_, lean_object* v_entries_1794_){
_start:
{
size_t v_depth_boxed_1795_; lean_object* v_res_1796_; 
v_depth_boxed_1795_ = lean_unbox_usize(v_depth_1790_);
lean_dec(v_depth_1790_);
v_res_1796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1795_, v_keys_1791_, v_vals_1792_, v_i_1793_, v_entries_1794_);
lean_dec_ref(v_vals_1792_);
lean_dec_ref(v_keys_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
size_t v_x_18470__boxed_1802_; size_t v_x_18471__boxed_1803_; lean_object* v_res_1804_; 
v_x_18470__boxed_1802_ = lean_unbox_usize(v_x_1798_);
lean_dec(v_x_1798_);
v_x_18471__boxed_1803_ = lean_unbox_usize(v_x_1799_);
lean_dec(v_x_1799_);
v_res_1804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1797_, v_x_18470__boxed_1802_, v_x_18471__boxed_1803_, v_x_1800_, v_x_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
uint64_t v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = l_Lean_instHashableMVarId_hash(v_x_1806_);
v___x_1809_ = lean_uint64_to_usize(v___x_1808_);
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1805_, v___x_1809_, v___x_1810_, v_x_1806_, v_x_1807_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1812_, lean_object* v_val_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_mctx_1817_; lean_object* v_cache_1818_; lean_object* v_zetaDeltaFVarIds_1819_; lean_object* v_postponed_1820_; lean_object* v_diag_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1850_; 
v___x_1816_ = lean_st_ref_take(v___y_1814_);
v_mctx_1817_ = lean_ctor_get(v___x_1816_, 0);
v_cache_1818_ = lean_ctor_get(v___x_1816_, 1);
v_zetaDeltaFVarIds_1819_ = lean_ctor_get(v___x_1816_, 2);
v_postponed_1820_ = lean_ctor_get(v___x_1816_, 3);
v_diag_1821_ = lean_ctor_get(v___x_1816_, 4);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1823_ = v___x_1816_;
v_isShared_1824_ = v_isSharedCheck_1850_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_diag_1821_);
lean_inc(v_postponed_1820_);
lean_inc(v_zetaDeltaFVarIds_1819_);
lean_inc(v_cache_1818_);
lean_inc(v_mctx_1817_);
lean_dec(v___x_1816_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1850_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_depth_1825_; lean_object* v_levelAssignDepth_1826_; lean_object* v_lmvarCounter_1827_; lean_object* v_mvarCounter_1828_; lean_object* v_lDecls_1829_; lean_object* v_decls_1830_; lean_object* v_userNames_1831_; lean_object* v_lAssignment_1832_; lean_object* v_eAssignment_1833_; lean_object* v_dAssignment_1834_; lean_object* v_instanceTypedMVars_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1849_; 
v_depth_1825_ = lean_ctor_get(v_mctx_1817_, 0);
v_levelAssignDepth_1826_ = lean_ctor_get(v_mctx_1817_, 1);
v_lmvarCounter_1827_ = lean_ctor_get(v_mctx_1817_, 2);
v_mvarCounter_1828_ = lean_ctor_get(v_mctx_1817_, 3);
v_lDecls_1829_ = lean_ctor_get(v_mctx_1817_, 4);
v_decls_1830_ = lean_ctor_get(v_mctx_1817_, 5);
v_userNames_1831_ = lean_ctor_get(v_mctx_1817_, 6);
v_lAssignment_1832_ = lean_ctor_get(v_mctx_1817_, 7);
v_eAssignment_1833_ = lean_ctor_get(v_mctx_1817_, 8);
v_dAssignment_1834_ = lean_ctor_get(v_mctx_1817_, 9);
v_instanceTypedMVars_1835_ = lean_ctor_get(v_mctx_1817_, 10);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_mctx_1817_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1837_ = v_mctx_1817_;
v_isShared_1838_ = v_isSharedCheck_1849_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_instanceTypedMVars_1835_);
lean_inc(v_dAssignment_1834_);
lean_inc(v_eAssignment_1833_);
lean_inc(v_lAssignment_1832_);
lean_inc(v_userNames_1831_);
lean_inc(v_decls_1830_);
lean_inc(v_lDecls_1829_);
lean_inc(v_mvarCounter_1828_);
lean_inc(v_lmvarCounter_1827_);
lean_inc(v_levelAssignDepth_1826_);
lean_inc(v_depth_1825_);
lean_dec(v_mctx_1817_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1849_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1833_, v_mvarId_1812_, v_val_1813_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 8, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_depth_1825_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_levelAssignDepth_1826_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_lmvarCounter_1827_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_mvarCounter_1828_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_lDecls_1829_);
lean_ctor_set(v_reuseFailAlloc_1848_, 5, v_decls_1830_);
lean_ctor_set(v_reuseFailAlloc_1848_, 6, v_userNames_1831_);
lean_ctor_set(v_reuseFailAlloc_1848_, 7, v_lAssignment_1832_);
lean_ctor_set(v_reuseFailAlloc_1848_, 8, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1848_, 9, v_dAssignment_1834_);
lean_ctor_set(v_reuseFailAlloc_1848_, 10, v_instanceTypedMVars_1835_);
v___x_1841_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1841_);
v___x_1843_ = v___x_1823_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_cache_1818_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_zetaDeltaFVarIds_1819_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_postponed_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_diag_1821_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_st_ref_put(v___y_1814_, v___x_1843_);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_1851_, lean_object* v_val_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_1851_, v_val_1852_, v___y_1853_);
lean_dec(v___y_1853_);
return v_res_1855_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_14959__overap_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_14959__overap_1866_ = lean_panic_fn_borrowed(v___x_1865_, v_msg_1857_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
lean_inc(v___y_1859_);
lean_inc_ref(v___y_1858_);
v___x_1867_ = lean_apply_7(v___x_14959__overap_1866_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, lean_box(0));
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_1877_, size_t v_i_1878_, size_t v_stop_1879_, lean_object* v_b_1880_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_eq(v_i_1878_, v_stop_1879_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v_fst_1883_; lean_object* v_snd_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; 
v___x_1882_ = lean_array_uget_borrowed(v_as_1877_, v_i_1878_);
v_fst_1883_ = lean_ctor_get(v___x_1882_, 0);
v_snd_1884_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_snd_1884_);
v___x_1885_ = l_Lean_mkFVar(v_snd_1884_);
lean_inc(v_fst_1883_);
v___x_1886_ = l_Lean_Meta_FVarSubst_insert(v_b_1880_, v_fst_1883_, v___x_1885_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1878_, v___x_1887_);
v_i_1878_ = v___x_1888_;
v_b_1880_ = v___x_1886_;
goto _start;
}
else
{
return v_b_1880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_1890_, lean_object* v_i_1891_, lean_object* v_stop_1892_, lean_object* v_b_1893_){
_start:
{
size_t v_i_boxed_1894_; size_t v_stop_boxed_1895_; lean_object* v_res_1896_; 
v_i_boxed_1894_ = lean_unbox_usize(v_i_1891_);
lean_dec(v_i_1891_);
v_stop_boxed_1895_ = lean_unbox_usize(v_stop_1892_);
lean_dec(v_stop_1892_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_1890_, v_i_boxed_1894_, v_stop_boxed_1895_, v_b_1893_);
lean_dec_ref(v_as_1890_);
return v_res_1896_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1897_; lean_object* v_dummy_1898_; 
v___x_1897_ = lean_box(0);
v_dummy_1898_ = l_Lean_Expr_sort___override(v___x_1897_);
return v_dummy_1898_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_1903_ = lean_unsigned_to_nat(62u);
v___x_1904_ = lean_unsigned_to_nat(323u);
v___x_1905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_1906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_1907_ = l_mkPanicMessageWithDecl(v___x_1906_, v___x_1905_, v___x_1904_, v___x_1903_, v___x_1902_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v_snd_1910_, lean_object* v___x_1911_, lean_object* v___x_1912_, lean_object* v___x_1913_, lean_object* v_e_1914_, lean_object* v___x_1915_, lean_object* v_head_1916_, lean_object* v_fst_1917_, lean_object* v_tail_1918_, uint8_t v___x_1919_, lean_object* v_snd_1920_, lean_object* v___x_1921_, lean_object* v_fs_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Meta_getElimInfo(v___x_1908_, v___x_1909_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
lean_inc(v_snd_1910_);
v___x_1932_ = l_Lean_MVarId_getTag(v_snd_1910_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
lean_inc(v_a_1931_);
v___x_1934_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_1931_, v___x_1911_, v_a_1933_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_elimApp_1936_; lean_object* v_alts_1937_; lean_object* v_motivePos_1938_; lean_object* v_nargs_1939_; lean_object* v_dummy_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_elimApp_1936_ = lean_ctor_get(v_a_1935_, 0);
lean_inc_ref_n(v_elimApp_1936_, 2);
v_alts_1937_ = lean_ctor_get(v_a_1935_, 3);
lean_inc_ref(v_alts_1937_);
lean_dec(v_a_1935_);
v_motivePos_1938_ = lean_ctor_get(v_a_1931_, 2);
lean_inc(v_motivePos_1938_);
lean_dec(v_a_1931_);
v_nargs_1939_ = l_Lean_Expr_getAppNumArgs(v_elimApp_1936_);
v_dummy_1940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
lean_inc(v_nargs_1939_);
v___x_1941_ = lean_mk_array(v_nargs_1939_, v_dummy_1940_);
v___x_1942_ = lean_nat_sub(v_nargs_1939_, v___x_1912_);
lean_dec(v_nargs_1939_);
v___x_1943_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_1936_, v___x_1941_, v___x_1942_);
v___x_1944_ = lean_array_get(v___x_1913_, v___x_1943_, v_motivePos_1938_);
lean_dec(v_motivePos_1938_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l_Lean_Expr_mvarId_x21(v___x_1944_);
lean_dec(v___x_1944_);
v___x_1946_ = l_Lean_Expr_fvarId_x21(v_e_1914_);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1912_);
lean_inc_ref(v___x_1947_);
v___x_1948_ = lean_array_push(v___x_1947_, v___x_1946_);
v___x_1949_ = lean_mk_empty_array_with_capacity(v___x_1915_);
lean_inc(v_snd_1910_);
v___x_1950_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_1910_, v___x_1945_, v___x_1948_, v___x_1949_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref_known(v___x_1950_, 1);
v___x_1951_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_1910_, v_elimApp_1936_, v___y_1926_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
lean_dec_ref_known(v___x_1951_, 1);
v___x_1952_ = lean_array_get_size(v_alts_1937_);
v___x_1953_ = lean_nat_dec_eq(v___x_1952_, v___x_1912_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_alts_1937_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
v___x_1954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4);
v___x_1955_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_1954_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v_name_1957_; lean_object* v_mvarId_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2030_; 
v___x_1956_ = lean_array_fget(v_alts_1937_, v___x_1915_);
lean_dec_ref(v_alts_1937_);
v_name_1957_ = lean_ctor_get(v___x_1956_, 0);
v_mvarId_1958_ = lean_ctor_get(v___x_1956_, 2);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_1956_, 1);
lean_dec(v_unused_2031_);
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_2030_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_mvarId_1958_);
lean_inc(v_name_1957_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2030_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_MVarId_intro(v_mvarId_1958_, v_head_1916_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_fst_1964_; lean_object* v_snd_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2021_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v_fst_1964_ = lean_ctor_get(v_a_1963_, 0);
v_snd_1965_ = lean_ctor_get(v_a_1963_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1963_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1967_ = v_a_1963_;
v_isShared_1968_ = v_isSharedCheck_2021_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snd_1965_);
lean_inc(v_fst_1964_);
lean_dec(v_a_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2021_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_array_get_size(v_fst_1917_);
v___x_1970_ = l_Lean_Meta_introNCore(v_snd_1965_, v___x_1969_, v_tail_1918_, v___x_1919_, v___x_1953_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2012_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_2012_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2012_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2011_; 
v_fst_1975_ = lean_ctor_get(v_a_1971_, 0);
v_snd_1976_ = lean_ctor_get(v_a_1971_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1978_ = v_a_1971_;
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_snd_1976_);
lean_inc(v_fst_1975_);
lean_dec(v_a_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___y_1981_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = l_Array_zip___redArg(v_fst_1917_, v_fst_1975_);
lean_dec(v_fst_1975_);
v___x_2002_ = lean_array_get_size(v___x_2001_);
v___x_2003_ = lean_nat_dec_lt(v___x_1915_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_2001_);
v___y_1981_ = v_fs_1922_;
goto v___jp_1980_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_nat_dec_le(v___x_2002_, v___x_2002_);
if (v___x_2004_ == 0)
{
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_2001_);
v___y_1981_ = v_fs_1922_;
goto v___jp_1980_;
}
else
{
size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = lean_usize_of_nat(v___x_2002_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2001_, v___x_2005_, v___x_2006_, v_fs_1922_);
lean_dec_ref(v___x_2001_);
v___y_1981_ = v___x_2007_;
goto v___jp_1980_;
}
}
else
{
size_t v___x_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = ((size_t)0ULL);
v___x_2009_ = lean_usize_of_nat(v___x_2002_);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2001_, v___x_2008_, v___x_2009_, v_fs_1922_);
lean_dec_ref(v___x_2001_);
v___y_1981_ = v___x_2010_;
goto v___jp_1980_;
}
}
v___jp_1980_:
{
lean_object* v___x_1983_; 
lean_inc(v_name_1957_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v_snd_1920_);
lean_ctor_set(v___x_1978_, 0, v_name_1957_);
v___x_1983_ = v___x_1978_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_name_1957_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_snd_1920_);
v___x_1983_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_mkFVar(v_fst_1964_);
v___x_1987_ = lean_array_push(v___x_1921_, v___x_1986_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 2, v___y_1981_);
lean_ctor_set(v___x_1960_, 1, v___x_1987_);
lean_ctor_set(v___x_1960_, 0, v_snd_1976_);
v___x_1989_ = v___x_1960_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_snd_1976_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v___y_1981_);
v___x_1989_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_name_1957_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_array_push(v___x_1947_, v___x_1991_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___x_1992_);
lean_ctor_set(v___x_1967_, 0, v___x_1985_);
v___x_1994_ = v___x_1967_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1994_);
v___x_1996_ = v___x_1973_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
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
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_1967_);
lean_dec(v_fst_1964_);
lean_del_object(v___x_1960_);
lean_dec(v_name_1957_);
lean_dec_ref(v___x_1947_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
v_a_2013_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1970_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1970_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_1960_);
lean_dec(v_name_1957_);
lean_dec_ref(v___x_1947_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
v_a_2022_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1962_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1962_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_alts_1937_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
v_a_2032_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1951_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1951_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_alts_1937_);
lean_dec_ref(v_elimApp_1936_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
lean_dec(v_snd_1910_);
v_a_2040_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1950_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1950_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_1931_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
lean_dec(v_snd_1910_);
v_a_2048_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1934_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1934_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_a_1931_);
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
lean_dec_ref(v___x_1911_);
lean_dec(v_snd_1910_);
v_a_2056_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1932_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1932_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_fs_1922_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
lean_dec(v_tail_1918_);
lean_dec(v_head_1916_);
lean_dec_ref(v___x_1911_);
lean_dec(v_snd_1910_);
v_a_2064_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_1930_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_1930_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2072_ = _args[0];
lean_object* v___x_2073_ = _args[1];
lean_object* v_snd_2074_ = _args[2];
lean_object* v___x_2075_ = _args[3];
lean_object* v___x_2076_ = _args[4];
lean_object* v___x_2077_ = _args[5];
lean_object* v_e_2078_ = _args[6];
lean_object* v___x_2079_ = _args[7];
lean_object* v_head_2080_ = _args[8];
lean_object* v_fst_2081_ = _args[9];
lean_object* v_tail_2082_ = _args[10];
lean_object* v___x_2083_ = _args[11];
lean_object* v_snd_2084_ = _args[12];
lean_object* v___x_2085_ = _args[13];
lean_object* v_fs_2086_ = _args[14];
lean_object* v___y_2087_ = _args[15];
lean_object* v___y_2088_ = _args[16];
lean_object* v___y_2089_ = _args[17];
lean_object* v___y_2090_ = _args[18];
lean_object* v___y_2091_ = _args[19];
lean_object* v___y_2092_ = _args[20];
lean_object* v___y_2093_ = _args[21];
_start:
{
uint8_t v___x_18755__boxed_2094_; lean_object* v_res_2095_; 
v___x_18755__boxed_2094_ = lean_unbox(v___x_2083_);
v_res_2095_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2072_, v___x_2073_, v_snd_2074_, v___x_2075_, v___x_2076_, v___x_2077_, v_e_2078_, v___x_2079_, v_head_2080_, v_fst_2081_, v_tail_2082_, v___x_18755__boxed_2094_, v_snd_2084_, v___x_2085_, v_fs_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_fst_2081_);
lean_dec(v___x_2079_);
lean_dec_ref(v_e_2078_);
lean_dec_ref(v___x_2077_);
lean_dec(v___x_2076_);
return v_res_2095_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_2097_ = lean_unsigned_to_nat(76u);
v___x_2098_ = lean_unsigned_to_nat(315u);
v___x_2099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_2100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2101_ = l_mkPanicMessageWithDecl(v___x_2100_, v___x_2099_, v___x_2098_, v___x_2097_, v___x_2096_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(uint8_t v___x_2109_, lean_object* v_e_2110_, lean_object* v___x_2111_, lean_object* v_g_2112_, lean_object* v___x_2113_, lean_object* v_fs_2114_, lean_object* v_pat_2115_, lean_object* v_____r_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___y_2128_; uint8_t v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2172_; lean_object* v___x_2178_; 
v___x_2178_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2115_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2172_ = v___x_2179_;
goto v___jp_2171_;
}
else
{
lean_object* v_head_2180_; 
v_head_2180_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_head_2180_);
lean_dec_ref_known(v___x_2178_, 2);
v___y_2172_ = v_head_2180_;
goto v___jp_2171_;
}
v___jp_2124_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0);
v___x_2126_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2125_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2126_;
}
v___jp_2127_:
{
uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_fst_2139_; 
v___x_2131_ = 0;
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1));
v___x_2134_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1, v___x_2131_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 1, v___x_2109_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 2, v___x_2109_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 3, v___x_2109_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 4, v___x_2109_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 5, v___x_2109_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1 + 6, v___x_2109_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_mk_empty_array_with_capacity(v___x_2135_);
lean_inc_ref(v___x_2136_);
v___x_2137_ = lean_array_push(v___x_2136_, v___x_2134_);
v___x_2138_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2130_, v___x_2137_, v___y_2129_, v___x_2132_, v___y_2128_);
lean_dec_ref(v___x_2137_);
v_fst_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_fst_2139_);
if (lean_obj_tag(v_fst_2139_) == 1)
{
lean_object* v_tail_2140_; 
v_tail_2140_ = lean_ctor_get(v_fst_2139_, 1);
lean_inc(v_tail_2140_);
if (lean_obj_tag(v_tail_2140_) == 0)
{
lean_object* v_snd_2141_; lean_object* v_head_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_snd_2141_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2141_);
lean_dec_ref(v___x_2138_);
v_head_2142_ = lean_ctor_get(v_fst_2139_, 0);
lean_inc(v_head_2142_);
lean_dec_ref_known(v_fst_2139_, 2);
lean_inc_ref(v_e_2110_);
lean_inc_ref(v___x_2136_);
v___x_2143_ = lean_array_push(v___x_2136_, v_e_2110_);
v___x_2144_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2143_, v___x_2111_, v___x_2109_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_MVarId_revert(v_g_2112_, v_a_2145_, v___x_2109_, v___x_2109_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v_fst_2148_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_fst_2148_);
v_snd_2149_ = lean_ctor_get(v_a_2147_, 1);
lean_inc_n(v_snd_2149_, 2);
lean_dec(v_a_2147_);
v___x_2150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4));
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_box(v___x_2109_);
v___f_2153_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed), 22, 15);
lean_closure_set(v___f_2153_, 0, v___x_2150_);
lean_closure_set(v___f_2153_, 1, v___x_2151_);
lean_closure_set(v___f_2153_, 2, v_snd_2149_);
lean_closure_set(v___f_2153_, 3, v___x_2143_);
lean_closure_set(v___f_2153_, 4, v___x_2135_);
lean_closure_set(v___f_2153_, 5, v___x_2113_);
lean_closure_set(v___f_2153_, 6, v_e_2110_);
lean_closure_set(v___f_2153_, 7, v___x_2132_);
lean_closure_set(v___f_2153_, 8, v_head_2142_);
lean_closure_set(v___f_2153_, 9, v_fst_2148_);
lean_closure_set(v___f_2153_, 10, v_tail_2140_);
lean_closure_set(v___f_2153_, 11, v___x_2152_);
lean_closure_set(v___f_2153_, 12, v_snd_2141_);
lean_closure_set(v___f_2153_, 13, v___x_2136_);
lean_closure_set(v___f_2153_, 14, v_fs_2114_);
v___x_2154_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2149_, v___f_2153_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2154_;
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v___x_2143_);
lean_dec(v_head_2142_);
lean_dec(v_snd_2141_);
lean_dec_ref(v___x_2136_);
lean_dec(v_fs_2114_);
lean_dec_ref(v___x_2113_);
lean_dec_ref(v_e_2110_);
v_a_2155_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2146_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2146_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v___x_2143_);
lean_dec(v_head_2142_);
lean_dec(v_snd_2141_);
lean_dec_ref(v___x_2136_);
lean_dec(v_fs_2114_);
lean_dec_ref(v___x_2113_);
lean_dec(v_g_2112_);
lean_dec_ref(v_e_2110_);
v_a_2163_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2144_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2144_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_dec(v_tail_2140_);
lean_dec_ref_known(v_fst_2139_, 2);
lean_dec_ref(v___x_2138_);
lean_dec_ref(v___x_2136_);
lean_dec(v_fs_2114_);
lean_dec_ref(v___x_2113_);
lean_dec(v_g_2112_);
lean_dec(v___x_2111_);
lean_dec_ref(v_e_2110_);
goto v___jp_2124_;
}
}
else
{
lean_dec(v_fst_2139_);
lean_dec_ref(v___x_2138_);
lean_dec_ref(v___x_2136_);
lean_dec(v_fs_2114_);
lean_dec_ref(v___x_2113_);
lean_dec(v_g_2112_);
lean_dec(v___x_2111_);
lean_dec_ref(v_e_2110_);
goto v___jp_2124_;
}
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v_ref_2176_; uint8_t v___x_2177_; 
lean_inc_ref(v___y_2172_);
v___x_2173_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2172_);
v_fst_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_fst_2174_);
v_snd_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_snd_2175_);
lean_dec_ref(v___x_2173_);
v_ref_2176_ = lean_ctor_get(v___y_2172_, 0);
lean_inc(v_ref_2176_);
lean_dec_ref(v___y_2172_);
v___x_2177_ = lean_unbox(v_fst_2174_);
lean_dec(v_fst_2174_);
v___y_2128_ = v_snd_2175_;
v___y_2129_ = v___x_2177_;
v___y_2130_ = v_ref_2176_;
goto v___jp_2127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v___x_2181_, lean_object* v_e_2182_, lean_object* v___x_2183_, lean_object* v_g_2184_, lean_object* v___x_2185_, lean_object* v_fs_2186_, lean_object* v_pat_2187_, lean_object* v_____r_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v___x_19127__boxed_2196_; lean_object* v_res_2197_; 
v___x_19127__boxed_2196_ = lean_unbox(v___x_2181_);
v_res_2197_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_19127__boxed_2196_, v_e_2182_, v___x_2183_, v_g_2184_, v___x_2185_, v_fs_2186_, v_pat_2187_, v_____r_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2197_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
if (lean_obj_tag(v_x_2198_) == 0)
{
if (lean_obj_tag(v_x_2199_) == 0)
{
uint8_t v___x_2200_; 
v___x_2200_ = 1;
return v___x_2200_;
}
else
{
uint8_t v___x_2201_; 
v___x_2201_ = 0;
return v___x_2201_;
}
}
else
{
if (lean_obj_tag(v_x_2199_) == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = 0;
return v___x_2202_;
}
else
{
lean_object* v_val_2203_; lean_object* v_val_2204_; uint8_t v___x_2205_; 
v_val_2203_ = lean_ctor_get(v_x_2198_, 0);
v_val_2204_ = lean_ctor_get(v_x_2199_, 0);
v___x_2205_ = lean_name_eq(v_val_2203_, v_val_2204_);
return v___x_2205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_2206_, v_x_2207_);
lean_dec(v_x_2207_);
lean_dec(v_x_2206_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_2214_ = l_Lean_MessageData_ofFormat(v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
if (lean_obj_tag(v_x_2216_) == 0)
{
return v_x_2215_;
}
else
{
lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2240_; 
v_head_2217_ = lean_ctor_get(v_x_2216_, 0);
v_tail_2218_ = lean_ctor_get(v_x_2216_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_x_2216_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2220_ = v_x_2216_;
v_isShared_2221_ = v_isSharedCheck_2240_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_tail_2218_);
lean_inc(v_head_2217_);
lean_dec(v_x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2240_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_before_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2238_; 
v_before_2222_ = lean_ctor_get(v_head_2217_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_head_2217_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v_head_2217_, 1);
lean_dec(v_unused_2239_);
v___x_2224_ = v_head_2217_;
v_isShared_2225_ = v_isSharedCheck_2238_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_before_2222_);
lean_dec(v_head_2217_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2238_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 7);
lean_ctor_set(v___x_2224_, 1, v___x_2226_);
lean_ctor_set(v___x_2224_, 0, v_x_2215_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_x_2215_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_2221_ == 0)
{
lean_ctor_set_tag(v___x_2220_, 7);
lean_ctor_set(v___x_2220_, 1, v___x_2229_);
lean_ctor_set(v___x_2220_, 0, v___x_2228_);
v___x_2231_ = v___x_2220_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = l_Lean_MessageData_ofSyntax(v_before_2222_);
v___x_2233_ = l_Lean_indentD(v___x_2232_);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2231_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v_x_2215_ = v___x_2234_;
v_x_2216_ = v_tail_2218_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_2241_, lean_object* v_opt_2242_){
_start:
{
lean_object* v_name_2243_; lean_object* v_defValue_2244_; lean_object* v_map_2245_; lean_object* v___x_2246_; 
v_name_2243_ = lean_ctor_get(v_opt_2242_, 0);
v_defValue_2244_ = lean_ctor_get(v_opt_2242_, 1);
v_map_2245_ = lean_ctor_get(v_opts_2241_, 0);
v___x_2246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2245_, v_name_2243_);
if (lean_obj_tag(v___x_2246_) == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_unbox(v_defValue_2244_);
return v___x_2247_;
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2246_, 1);
if (lean_obj_tag(v_val_2248_) == 1)
{
uint8_t v_v_2249_; 
v_v_2249_ = lean_ctor_get_uint8(v_val_2248_, 0);
lean_dec_ref_known(v_val_2248_, 0);
return v_v_2249_;
}
else
{
uint8_t v___x_2250_; 
lean_dec(v_val_2248_);
v___x_2250_ = lean_unbox(v_defValue_2244_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_2251_, lean_object* v_opt_2252_){
_start:
{
uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_res_2253_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_2251_, v_opt_2252_);
lean_dec_ref(v_opt_2252_);
lean_dec_ref(v_opts_2251_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_2259_ = l_Lean_MessageData_ofFormat(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_2260_, lean_object* v_macroStack_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_toCold_2264_; lean_object* v_options_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_toCold_2264_ = lean_ctor_get(v___y_2262_, 0);
v_options_2265_ = lean_ctor_get(v_toCold_2264_, 2);
v___x_2266_ = l_Lean_Elab_pp_macroStack;
v___x_2267_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_options_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec(v_macroStack_2261_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_msgData_2260_);
return v___x_2268_;
}
else
{
if (lean_obj_tag(v_macroStack_2261_) == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_msgData_2260_);
return v___x_2269_;
}
else
{
lean_object* v_head_2270_; lean_object* v_after_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2286_; 
v_head_2270_ = lean_ctor_get(v_macroStack_2261_, 0);
lean_inc(v_head_2270_);
v_after_2271_ = lean_ctor_get(v_head_2270_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_head_2270_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_head_2270_, 0);
lean_dec(v_unused_2287_);
v___x_2273_ = v_head_2270_;
v_isShared_2274_ = v_isSharedCheck_2286_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_after_2271_);
lean_dec(v_head_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2286_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2274_ == 0)
{
lean_ctor_set_tag(v___x_2273_, 7);
lean_ctor_set(v___x_2273_, 1, v___x_2275_);
lean_ctor_set(v___x_2273_, 0, v_msgData_2260_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_msgData_2260_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v_msgData_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2278_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_MessageData_ofSyntax(v_after_2271_);
v___x_2281_ = l_Lean_indentD(v___x_2280_);
v_msgData_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2282_, 0, v___x_2279_);
lean_ctor_set(v_msgData_2282_, 1, v___x_2281_);
v___x_2283_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_2282_, v_macroStack_2261_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_2288_, lean_object* v_macroStack_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_2288_, v_macroStack_2289_, v___y_2290_);
lean_dec_ref(v___y_2290_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_ref_2301_; lean_object* v___x_2302_; lean_object* v_a_2303_; lean_object* v_macroStack_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_ref_2301_ = lean_ctor_get(v___y_2298_, 2);
v___x_2302_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_2293_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v_macroStack_2304_ = lean_ctor_get(v___y_2294_, 1);
v___x_2305_ = l_Lean_Elab_getBetterRef(v_ref_2301_, v_macroStack_2304_);
lean_inc(v_macroStack_2304_);
v___x_2306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_2303_, v_macroStack_2304_, v___y_2298_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2305_);
lean_ctor_set(v___x_2311_, 1, v_a_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 1);
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2324_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0));
v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v_00_u03b1_2333_, lean_object* v_x_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2342_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_2343_ = l_Lean_MessageData_ofExpr(v_e_2331_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = l_Lean_MessageData_ofExpr(v_a_2332_);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_2350_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object* v_e_2352_, lean_object* v_a_2353_, lean_object* v_00_u03b1_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2352_, v_a_2353_, v_00_u03b1_2354_, v_x_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_e_2506_, lean_object* v___y_2507_, lean_object* v_asFVar_2508_, lean_object* v_a_2509_, lean_object* v_fs_2510_, lean_object* v_clears_2511_, lean_object* v_cont_2512_, lean_object* v___x_2513_, lean_object* v_g_2514_, lean_object* v___x_2515_, lean_object* v_pat_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___y_2526_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___y_2561_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2573_ = lean_box(0);
lean_inc_ref(v_e_2506_);
v___x_2574_ = l_Lean_Expr_mdata___override(v___x_2573_, v_e_2506_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_box(0);
v___x_2577_ = 0;
lean_inc(v___y_2507_);
v___x_2578_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2507_, v___x_2574_, v___x_2575_, v___x_2575_, v___x_2576_, v___x_2577_, v___x_2577_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2578_, 1);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc_ref(v_e_2506_);
v___x_2579_ = lean_apply_6(v_asFVar_2508_, v_e_2506_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, lean_box(0));
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
lean_inc_ref(v_e_2506_);
v___x_2581_ = lean_infer_type(v_e_2506_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec(v___y_2507_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2506_, v_a_2584_, lean_box(0), v___x_2590_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
lean_dec(v___y_2507_);
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
lean_inc(v_fs_2510_);
v___x_2596_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2577_, v_e_2506_, v___x_2513_, v_g_2514_, v___x_2515_, v_fs_2510_, v_pat_2516_, v___x_2595_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2596_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_box(0);
lean_inc_ref(v_e_2506_);
v___x_2598_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2506_, v_a_2584_, lean_box(0), v___x_2597_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
lean_inc(v_fs_2510_);
v___x_2600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2577_, v_e_2506_, v___x_2513_, v_g_2514_, v___x_2515_, v_fs_2510_, v_pat_2516_, v_a_2599_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2600_;
goto v___jp_2560_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v___x_2515_);
lean_dec(v___x_2513_);
v_val_2609_ = lean_ctor_get(v_val_2592_, 0);
lean_inc_ref(v_val_2609_);
lean_dec_ref_known(v_val_2592_, 1);
v_numParams_2610_ = lean_ctor_get(v_val_2609_, 1);
lean_inc(v_numParams_2610_);
v_ctors_2611_ = lean_ctor_get(v_val_2609_, 4);
lean_inc(v_ctors_2611_);
lean_dec_ref(v_val_2609_);
v___x_2612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2613_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2516_);
v___x_2614_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2507_, v_numParams_2610_, v___x_2612_, v_ctors_2611_, v___x_2613_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
v___x_2618_ = l_Lean_Expr_fvarId_x21(v_e_2506_);
lean_dec_ref(v_e_2506_);
v___x_2619_ = 1;
v___x_2620_ = l_Lean_MVarId_cases(v_g_2514_, v___x_2618_, v_fst_2616_, v___x_2619_, v___x_2575_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
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
lean_dec(v_g_2514_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec(v___y_2507_);
v___x_2638_ = lean_box(0);
v___x_2639_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2506_, v_a_2584_, lean_box(0), v___x_2638_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec(v___y_2507_);
v___x_2640_ = lean_box(0);
v___x_2641_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2506_, v_a_2584_, lean_box(0), v___x_2640_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
v___y_2561_ = v___x_2641_;
goto v___jp_2560_;
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec(v___y_2507_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec(v___y_2507_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec(v___y_2507_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec(v___y_2507_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_pat_2516_);
lean_dec_ref(v___x_2515_);
lean_dec(v_g_2514_);
lean_dec(v___x_2513_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_asFVar_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v_e_2506_);
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
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2509_);
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; uint8_t v___x_2552_; 
lean_inc(v_a_2509_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_fst_2545_);
lean_ctor_set(v___x_2551_, 1, v_a_2509_);
v___x_2552_ = lean_nat_dec_le(v___x_2548_, v___x_2548_);
if (v___x_2552_ == 0)
{
if (v___x_2549_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref_known(v___x_2551_, 2);
lean_dec_ref(v_snd_2546_);
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2509_);
return v___x_2553_;
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
lean_dec(v_a_2509_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2548_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2510_, v_clears_2511_, v_cont_2512_, v_snd_2546_, v___x_2554_, v___x_2555_, v___x_2551_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v_snd_2546_);
v___y_2526_ = v___x_2556_;
goto v___jp_2525_;
}
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_a_2509_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2548_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2510_, v_clears_2511_, v_cont_2512_, v_snd_2546_, v___x_2557_, v___x_2558_, v___x_2551_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
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
lean_dec_ref(v_cont_2512_);
lean_dec_ref(v_clears_2511_);
lean_dec(v_fs_2510_);
lean_dec(v_a_2509_);
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
lean_object* v_e_2682_ = _args[0];
lean_object* v___y_2683_ = _args[1];
lean_object* v_asFVar_2684_ = _args[2];
lean_object* v_a_2685_ = _args[3];
lean_object* v_fs_2686_ = _args[4];
lean_object* v_clears_2687_ = _args[5];
lean_object* v_cont_2688_ = _args[6];
lean_object* v___x_2689_ = _args[7];
lean_object* v_g_2690_ = _args[8];
lean_object* v___x_2691_ = _args[9];
lean_object* v_pat_2692_ = _args[10];
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
v_res_2701_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_e_2682_, v___y_2683_, v_asFVar_2684_, v_a_2685_, v_fs_2686_, v_clears_2687_, v_cont_2688_, v___x_2689_, v_g_2690_, v___x_2691_, v_pat_2692_, v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
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
lean_object* v_asFVar_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_e_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; lean_object* v___y_2931_; lean_object* v_ref_2942_; 
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
v_ref_2942_ = lean_ctor_get(v_pat_2915_, 0);
lean_inc(v_ref_2942_);
v___y_2931_ = v_ref_2942_;
goto v___jp_2930_;
v___jp_2930_:
{
lean_object* v_toCold_2932_; lean_object* v_currRecDepth_2933_; lean_object* v_ref_2934_; uint8_t v_diag_2935_; uint8_t v_suppressElabErrors_2936_; lean_object* v___f_2937_; lean_object* v___y_2938_; lean_object* v_ref_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_toCold_2932_ = lean_ctor_get(v_a_2921_, 0);
v_currRecDepth_2933_ = lean_ctor_get(v_a_2921_, 1);
v_ref_2934_ = lean_ctor_get(v_a_2921_, 2);
v_diag_2935_ = lean_ctor_get_uint8(v_a_2921_, sizeof(void*)*3);
v_suppressElabErrors_2936_ = lean_ctor_get_uint8(v_a_2921_, sizeof(void*)*3 + 1);
lean_inc_ref(v_pat_2915_);
lean_inc_n(v_g_2910_, 2);
lean_inc_ref(v_cont_2916_);
lean_inc_ref(v_clears_2912_);
lean_inc(v_fs_2911_);
lean_inc(v_a_2914_);
lean_inc(v___y_2931_);
lean_inc_ref(v_e_2927_);
v___f_2937_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2937_, 0, v_e_2927_);
lean_closure_set(v___f_2937_, 1, v___y_2931_);
lean_closure_set(v___f_2937_, 2, v_asFVar_2924_);
lean_closure_set(v___f_2937_, 3, v_a_2914_);
lean_closure_set(v___f_2937_, 4, v_fs_2911_);
lean_closure_set(v___f_2937_, 5, v_clears_2912_);
lean_closure_set(v___f_2937_, 6, v_cont_2916_);
lean_closure_set(v___f_2937_, 7, v___x_2925_);
lean_closure_set(v___f_2937_, 8, v_g_2910_);
lean_closure_set(v___f_2937_, 9, v___x_2926_);
lean_closure_set(v___f_2937_, 10, v_pat_2915_);
v___y_2938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2938_, 0, v_pat_2915_);
lean_closure_set(v___y_2938_, 1, v___f_2928_);
lean_closure_set(v___y_2938_, 2, v_e_2927_);
lean_closure_set(v___y_2938_, 3, v_asFVar_2924_);
lean_closure_set(v___y_2938_, 4, v_g_2910_);
lean_closure_set(v___y_2938_, 5, v_fs_2911_);
lean_closure_set(v___y_2938_, 6, v_cont_2916_);
lean_closure_set(v___y_2938_, 7, v_clears_2912_);
lean_closure_set(v___y_2938_, 8, v_a_2914_);
lean_closure_set(v___y_2938_, 9, v___f_2929_);
lean_closure_set(v___y_2938_, 10, v___f_2937_);
v_ref_2939_ = l_Lean_replaceRef(v___y_2931_, v_ref_2934_);
lean_dec(v___y_2931_);
lean_inc(v_currRecDepth_2933_);
lean_inc_ref(v_toCold_2932_);
v___x_2940_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2940_, 0, v_toCold_2932_);
lean_ctor_set(v___x_2940_, 1, v_currRecDepth_2933_);
lean_ctor_set(v___x_2940_, 2, v_ref_2939_);
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*3, v_diag_2935_);
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*3 + 1, v_suppressElabErrors_2936_);
v___x_2941_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2910_, v___y_2938_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v___x_2940_, v_a_2922_);
lean_dec_ref_known(v___x_2940_, 3);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2943_, lean_object* v_fs_2944_, lean_object* v_clears_2945_, lean_object* v_a_2946_, lean_object* v_pats_2947_, lean_object* v_cont_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
if (lean_obj_tag(v_pats_2947_) == 0)
{
lean_object* v___x_2956_; 
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
v___x_2956_ = lean_apply_11(v_cont_2948_, v_g_2943_, v_fs_2944_, v_clears_2945_, v_a_2946_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, lean_box(0));
return v___x_2956_;
}
else
{
lean_object* v_head_2957_; lean_object* v_tail_2958_; lean_object* v_fst_2959_; lean_object* v_snd_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; 
v_head_2957_ = lean_ctor_get(v_pats_2947_, 0);
lean_inc(v_head_2957_);
v_tail_2958_ = lean_ctor_get(v_pats_2947_, 1);
lean_inc(v_tail_2958_);
lean_dec_ref_known(v_pats_2947_, 2);
v_fst_2959_ = lean_ctor_get(v_head_2957_, 0);
lean_inc(v_fst_2959_);
v_snd_2960_ = lean_ctor_get(v_head_2957_, 1);
lean_inc(v_snd_2960_);
lean_dec(v_head_2957_);
v___f_2961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2961_, 0, v_tail_2958_);
lean_closure_set(v___f_2961_, 1, v_cont_2948_);
v___x_2962_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2943_, v_fs_2944_, v_clears_2945_, v_snd_2960_, v_a_2946_, v_fst_2959_, v___f_2961_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_snd_2960_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2963_, lean_object* v_cont_2964_, lean_object* v_g_2965_, lean_object* v_fs_2966_, lean_object* v_clears_2967_, lean_object* v_a_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2965_, v_fs_2966_, v_clears_2967_, v_a_2968_, v_tail_2963_, v_cont_2964_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2977_, lean_object* v_fs_2978_, lean_object* v_clears_2979_, lean_object* v_a_2980_, lean_object* v_pats_2981_, lean_object* v_cont_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2977_, v_fs_2978_, v_clears_2979_, v_a_2980_, v_pats_2981_, v_cont_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_2991_, lean_object* v_clears_2992_, lean_object* v_cont_2993_, lean_object* v_as_2994_, lean_object* v_i_2995_, lean_object* v_stop_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
size_t v_i_boxed_3005_; size_t v_stop_boxed_3006_; lean_object* v_res_3007_; 
v_i_boxed_3005_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_stop_boxed_3006_ = lean_unbox_usize(v_stop_2996_);
lean_dec(v_stop_2996_);
v_res_3007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2991_, v_clears_2992_, v_cont_2993_, v_as_2994_, v_i_boxed_3005_, v_stop_boxed_3006_, v_b_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_as_2994_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_3008_, lean_object* v_clears_3009_, lean_object* v_cont_3010_, lean_object* v_a_3011_, lean_object* v_goal_3012_, lean_object* v_ctorName_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3008_, v_clears_3009_, v_cont_3010_, v_a_3011_, v_goal_3012_, v_ctorName_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_ctorName_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3023_, lean_object* v_fs_3024_, lean_object* v_clears_3025_, lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_pat_3028_, lean_object* v_cont_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3023_, v_fs_3024_, v_clears_3025_, v_e_3026_, v_a_3027_, v_pat_3028_, v_cont_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec_ref(v_e_3026_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3038_, lean_object* v_g_3039_, lean_object* v_fs_3040_, lean_object* v_clears_3041_, lean_object* v_a_3042_, lean_object* v_pats_3043_, lean_object* v_cont_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3039_, v_fs_3040_, v_clears_3041_, v_a_3042_, v_pats_3043_, v_cont_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3053_, lean_object* v_g_3054_, lean_object* v_fs_3055_, lean_object* v_clears_3056_, lean_object* v_a_3057_, lean_object* v_pats_3058_, lean_object* v_cont_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3053_, v_g_3054_, v_fs_3055_, v_clears_3056_, v_a_3057_, v_pats_3058_, v_cont_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3068_, lean_object* v_fs_3069_, lean_object* v_clears_3070_, lean_object* v_cont_3071_, lean_object* v_a_3072_, lean_object* v_goal_3073_, lean_object* v_ctorName_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3069_, v_clears_3070_, v_cont_3071_, v_a_3072_, v_goal_3073_, v_ctorName_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3084_, lean_object* v_fs_3085_, lean_object* v_clears_3086_, lean_object* v_cont_3087_, lean_object* v_a_3088_, lean_object* v_goal_3089_, lean_object* v_ctorName_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3084_, v_fs_3085_, v_clears_3086_, v_cont_3087_, v_a_3088_, v_goal_3089_, v_ctorName_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_ctorName_3090_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3100_, lean_object* v_mvarId_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_mvarId_3112_, lean_object* v_x_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3111_, v_mvarId_3112_, v_x_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3122_, lean_object* v_g_3123_, lean_object* v_fs_3124_, lean_object* v_clears_3125_, lean_object* v_e_3126_, lean_object* v_a_3127_, lean_object* v_pat_3128_, lean_object* v_cont_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3123_, v_fs_3124_, v_clears_3125_, v_e_3126_, v_a_3127_, v_pat_3128_, v_cont_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_g_3139_, lean_object* v_fs_3140_, lean_object* v_clears_3141_, lean_object* v_e_3142_, lean_object* v_a_3143_, lean_object* v_pat_3144_, lean_object* v_cont_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3138_, v_g_3139_, v_fs_3140_, v_clears_3141_, v_e_3142_, v_a_3143_, v_pat_3144_, v_cont_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec_ref(v_e_3142_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3154_, lean_object* v_fs_3155_, lean_object* v_clears_3156_, lean_object* v_cont_3157_, lean_object* v_as_3158_, size_t v_i_3159_, size_t v_stop_3160_, lean_object* v_b_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3155_, v_clears_3156_, v_cont_3157_, v_as_3158_, v_i_3159_, v_stop_3160_, v_b_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3170_, lean_object* v_fs_3171_, lean_object* v_clears_3172_, lean_object* v_cont_3173_, lean_object* v_as_3174_, lean_object* v_i_3175_, lean_object* v_stop_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
size_t v_i_boxed_3185_; size_t v_stop_boxed_3186_; lean_object* v_res_3187_; 
v_i_boxed_3185_ = lean_unbox_usize(v_i_3175_);
lean_dec(v_i_3175_);
v_stop_boxed_3186_ = lean_unbox_usize(v_stop_3176_);
lean_dec(v_stop_3176_);
v_res_3187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3170_, v_fs_3171_, v_clears_3172_, v_cont_3173_, v_as_3174_, v_i_boxed_3185_, v_stop_boxed_3186_, v_b_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec_ref(v_as_3174_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3188_, lean_object* v_val_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3188_, v_val_3189_, v___y_3193_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3198_, lean_object* v_val_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3198_, v_val_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3208_, lean_object* v_msg_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3218_, lean_object* v_msg_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3218_, v_msg_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3229_, v_x_3230_, v_x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3233_, lean_object* v_macroStack_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3233_, v_macroStack_3234_, v___y_3239_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3243_, lean_object* v_macroStack_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3243_, v_macroStack_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3253_, lean_object* v_x_3254_, size_t v_x_3255_, size_t v_x_3256_, lean_object* v_x_3257_, lean_object* v_x_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3254_, v_x_3255_, v_x_3256_, v_x_3257_, v_x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
size_t v_x_20717__boxed_3266_; size_t v_x_20718__boxed_3267_; lean_object* v_res_3268_; 
v_x_20717__boxed_3266_ = lean_unbox_usize(v_x_3262_);
lean_dec(v_x_3262_);
v_x_20718__boxed_3267_ = lean_unbox_usize(v_x_3263_);
lean_dec(v_x_3263_);
v_res_3268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3260_, v_x_3261_, v_x_20717__boxed_3266_, v_x_20718__boxed_3267_, v_x_3264_, v_x_3265_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3269_, lean_object* v_n_3270_, lean_object* v_k_3271_, lean_object* v_v_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3270_, v_k_3271_, v_v_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3274_, size_t v_depth_3275_, lean_object* v_keys_3276_, lean_object* v_vals_3277_, lean_object* v_heq_3278_, lean_object* v_i_3279_, lean_object* v_entries_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3275_, v_keys_3276_, v_vals_3277_, v_i_3279_, v_entries_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_depth_3283_, lean_object* v_keys_3284_, lean_object* v_vals_3285_, lean_object* v_heq_3286_, lean_object* v_i_3287_, lean_object* v_entries_3288_){
_start:
{
size_t v_depth_boxed_3289_; lean_object* v_res_3290_; 
v_depth_boxed_3289_ = lean_unbox_usize(v_depth_3283_);
lean_dec(v_depth_3283_);
v_res_3290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3282_, v_depth_boxed_3289_, v_keys_3284_, v_vals_3285_, v_heq_3286_, v_i_3287_, v_entries_3288_);
lean_dec_ref(v_vals_3285_);
lean_dec_ref(v_keys_3284_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3291_, lean_object* v_x_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3292_, v_x_3293_, v_x_3294_, v_x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3297_, lean_object* v_as_3298_, size_t v_i_3299_, size_t v_stop_3300_){
_start:
{
uint8_t v___x_3301_; 
v___x_3301_ = lean_usize_dec_eq(v_i_3299_, v_stop_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = lean_array_uget_borrowed(v_as_3298_, v_i_3299_);
v___x_3303_ = l_Lean_instBEqFVarId_beq(v_a_3297_, v___x_3302_);
if (v___x_3303_ == 0)
{
size_t v___x_3304_; size_t v___x_3305_; 
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3299_, v___x_3304_);
v_i_3299_ = v___x_3305_;
goto _start;
}
else
{
return v___x_3303_;
}
}
else
{
uint8_t v___x_3307_; 
v___x_3307_ = 0;
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3308_, lean_object* v_as_3309_, lean_object* v_i_3310_, lean_object* v_stop_3311_){
_start:
{
size_t v_i_boxed_3312_; size_t v_stop_boxed_3313_; uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_i_boxed_3312_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_stop_boxed_3313_ = lean_unbox_usize(v_stop_3311_);
lean_dec(v_stop_3311_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3308_, v_as_3309_, v_i_boxed_3312_, v_stop_boxed_3313_);
lean_dec_ref(v_as_3309_);
lean_dec(v_a_3308_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3319_ = lean_array_get_size(v_as_3316_);
v___x_3320_ = lean_nat_dec_lt(v___x_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
return v___x_3320_;
}
else
{
if (v___x_3320_ == 0)
{
return v___x_3320_;
}
else
{
size_t v___x_3321_; size_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3319_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3317_, v_as_3316_, v___x_3321_, v___x_3322_);
return v___x_3323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3324_, lean_object* v_a_3325_){
_start:
{
uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_res_3326_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3324_, v_a_3325_);
lean_dec(v_a_3325_);
lean_dec_ref(v_as_3324_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3328_, v___y_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v_res_3333_; lean_object* v_r_3334_; 
v_res_3333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec(v_snd_3331_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3335_){
_start:
{
uint8_t v___x_3336_; 
v___x_3336_ = 0;
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3337_){
_start:
{
uint8_t v_res_3338_; lean_object* v_r_3339_; 
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3337_);
lean_dec(v_x_3337_);
v_r_3339_ = lean_box(v_res_3338_);
return v_r_3339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_unsigned_to_nat(16u);
v___x_3343_ = lean_mk_array(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v___x_3344_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3347_, size_t v_sz_3348_, size_t v_i_3349_, lean_object* v_b_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_lt(v_i_3349_, v_sz_3348_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_b_3350_);
return v___x_3354_;
}
else
{
lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3486_; 
v_snd_3355_ = lean_ctor_get(v_b_3350_, 1);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_b_3350_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v_b_3350_, 0);
lean_dec(v_unused_3487_);
v___x_3357_ = v_b_3350_;
v_isShared_3358_ = v_isSharedCheck_3486_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_dec(v_b_3350_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3486_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v_a_3361_; lean_object* v_a_3368_; 
v___x_3359_ = lean_box(0);
v_a_3368_ = lean_array_uget_borrowed(v_as_3347_, v_i_3349_);
if (lean_obj_tag(v_a_3368_) == 0)
{
v_a_3361_ = v_snd_3355_;
goto v___jp_3360_;
}
else
{
lean_object* v_val_3369_; uint8_t v_a_3371_; lean_object* v___f_3374_; lean_object* v___f_3375_; 
v_val_3369_ = lean_ctor_get(v_a_3368_, 0);
v___f_3374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3355_);
v___f_3375_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3375_, 0, v_snd_3355_);
if (lean_obj_tag(v_val_3369_) == 0)
{
lean_object* v_type_3376_; lean_object* v___x_3377_; uint8_t v_fst_3379_; lean_object* v_mctx_3380_; lean_object* v___y_3396_; lean_object* v_mctx_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_type_3376_ = lean_ctor_get(v_val_3369_, 3);
v___x_3377_ = lean_st_ref_get(v___y_3351_);
v_mctx_3401_ = lean_ctor_get(v___x_3377_, 0);
lean_inc_ref_n(v_mctx_3401_, 2);
lean_dec(v___x_3377_);
v___x_3402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v_mctx_3401_);
v___x_3404_ = l_Lean_Expr_hasFVar(v_type_3376_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
v___x_3405_ = l_Lean_Expr_hasMVar(v_type_3376_);
if (v___x_3405_ == 0)
{
lean_dec_ref_known(v___x_3403_, 2);
lean_dec_ref(v___f_3375_);
v_fst_3379_ = v___x_3405_;
v_mctx_3380_ = v_mctx_3401_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3406_; 
lean_dec_ref(v_mctx_3401_);
lean_inc_ref(v_type_3376_);
v___x_3406_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3376_, v___x_3403_);
v___y_3396_ = v___x_3406_;
goto v___jp_3395_;
}
}
else
{
lean_object* v___x_3407_; 
lean_dec_ref(v_mctx_3401_);
lean_inc_ref(v_type_3376_);
v___x_3407_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3376_, v___x_3403_);
v___y_3396_ = v___x_3407_;
goto v___jp_3395_;
}
v___jp_3378_:
{
lean_object* v___x_3381_; lean_object* v_cache_3382_; lean_object* v_zetaDeltaFVarIds_3383_; lean_object* v_postponed_3384_; lean_object* v_diag_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3393_; 
v___x_3381_ = lean_st_ref_take(v___y_3351_);
v_cache_3382_ = lean_ctor_get(v___x_3381_, 1);
v_zetaDeltaFVarIds_3383_ = lean_ctor_get(v___x_3381_, 2);
v_postponed_3384_ = lean_ctor_get(v___x_3381_, 3);
v_diag_3385_ = lean_ctor_get(v___x_3381_, 4);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3381_, 0);
lean_dec(v_unused_3394_);
v___x_3387_ = v___x_3381_;
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_diag_3385_);
lean_inc(v_postponed_3384_);
lean_inc(v_zetaDeltaFVarIds_3383_);
lean_inc(v_cache_3382_);
lean_dec(v___x_3381_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v_mctx_3380_);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_mctx_3380_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_cache_3382_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_zetaDeltaFVarIds_3383_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_postponed_3384_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_diag_3385_);
v___x_3390_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_st_ref_put(v___y_3351_, v___x_3390_);
v_a_3371_ = v_fst_3379_;
goto v___jp_3370_;
}
}
}
v___jp_3395_:
{
lean_object* v_snd_3397_; lean_object* v_fst_3398_; lean_object* v_mctx_3399_; uint8_t v___x_3400_; 
v_snd_3397_ = lean_ctor_get(v___y_3396_, 1);
lean_inc(v_snd_3397_);
v_fst_3398_ = lean_ctor_get(v___y_3396_, 0);
lean_inc(v_fst_3398_);
lean_dec_ref(v___y_3396_);
v_mctx_3399_ = lean_ctor_get(v_snd_3397_, 1);
lean_inc_ref(v_mctx_3399_);
lean_dec(v_snd_3397_);
v___x_3400_ = lean_unbox(v_fst_3398_);
lean_dec(v_fst_3398_);
v_fst_3379_ = v___x_3400_;
v_mctx_3380_ = v_mctx_3399_;
goto v___jp_3378_;
}
}
else
{
uint8_t v_nondep_3408_; 
v_nondep_3408_ = lean_ctor_get_uint8(v_val_3369_, sizeof(void*)*5);
if (v_nondep_3408_ == 0)
{
lean_object* v_type_3409_; lean_object* v_value_3410_; lean_object* v___x_3411_; uint8_t v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___y_3431_; uint8_t v_fst_3436_; lean_object* v_snd_3437_; lean_object* v___y_3443_; lean_object* v_mctx_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v_type_3409_ = lean_ctor_get(v_val_3369_, 3);
v_value_3410_ = lean_ctor_get(v_val_3369_, 4);
v___x_3411_ = lean_st_ref_get(v___y_3351_);
v_mctx_3447_ = lean_ctor_get(v___x_3411_, 0);
lean_inc_ref(v_mctx_3447_);
lean_dec(v___x_3411_);
v___x_3448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
lean_ctor_set(v___x_3449_, 1, v_mctx_3447_);
v___x_3450_ = l_Lean_Expr_hasFVar(v_type_3409_);
if (v___x_3450_ == 0)
{
uint8_t v___x_3451_; 
v___x_3451_ = l_Lean_Expr_hasMVar(v_type_3409_);
if (v___x_3451_ == 0)
{
v_fst_3436_ = v___x_3451_;
v_snd_3437_ = v___x_3449_;
goto v___jp_3435_;
}
else
{
lean_object* v___x_3452_; 
lean_inc_ref(v_type_3409_);
lean_inc_ref(v___f_3375_);
v___x_3452_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3409_, v___x_3449_);
v___y_3443_ = v___x_3452_;
goto v___jp_3442_;
}
}
else
{
lean_object* v___x_3453_; 
lean_inc_ref(v_type_3409_);
lean_inc_ref(v___f_3375_);
v___x_3453_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3409_, v___x_3449_);
v___y_3443_ = v___x_3453_;
goto v___jp_3442_;
}
v___jp_3412_:
{
lean_object* v_mctx_3415_; lean_object* v___x_3416_; lean_object* v_cache_3417_; lean_object* v_zetaDeltaFVarIds_3418_; lean_object* v_postponed_3419_; lean_object* v_diag_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3428_; 
v_mctx_3415_ = lean_ctor_get(v_snd_3414_, 1);
lean_inc_ref(v_mctx_3415_);
lean_dec_ref(v_snd_3414_);
v___x_3416_ = lean_st_ref_take(v___y_3351_);
v_cache_3417_ = lean_ctor_get(v___x_3416_, 1);
v_zetaDeltaFVarIds_3418_ = lean_ctor_get(v___x_3416_, 2);
v_postponed_3419_ = lean_ctor_get(v___x_3416_, 3);
v_diag_3420_ = lean_ctor_get(v___x_3416_, 4);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3429_);
v___x_3422_ = v___x_3416_;
v_isShared_3423_ = v_isSharedCheck_3428_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_diag_3420_);
lean_inc(v_postponed_3419_);
lean_inc(v_zetaDeltaFVarIds_3418_);
lean_inc(v_cache_3417_);
lean_dec(v___x_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3428_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_mctx_3415_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_mctx_3415_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_cache_3417_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_zetaDeltaFVarIds_3418_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_postponed_3419_);
lean_ctor_set(v_reuseFailAlloc_3427_, 4, v_diag_3420_);
v___x_3425_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_st_ref_put(v___y_3351_, v___x_3425_);
v_a_3371_ = v_fst_3413_;
goto v___jp_3370_;
}
}
}
v___jp_3430_:
{
lean_object* v_fst_3432_; lean_object* v_snd_3433_; uint8_t v___x_3434_; 
v_fst_3432_ = lean_ctor_get(v___y_3431_, 0);
lean_inc(v_fst_3432_);
v_snd_3433_ = lean_ctor_get(v___y_3431_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v___y_3431_);
v___x_3434_ = lean_unbox(v_fst_3432_);
lean_dec(v_fst_3432_);
v_fst_3413_ = v___x_3434_;
v_snd_3414_ = v_snd_3433_;
goto v___jp_3412_;
}
v___jp_3435_:
{
if (v_fst_3436_ == 0)
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Lean_Expr_hasFVar(v_value_3410_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = l_Lean_Expr_hasMVar(v_value_3410_);
if (v___x_3439_ == 0)
{
lean_dec_ref(v___f_3375_);
v_fst_3413_ = v___x_3439_;
v_snd_3414_ = v_snd_3437_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3440_; 
lean_inc_ref(v_value_3410_);
v___x_3440_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_value_3410_, v_snd_3437_);
v___y_3431_ = v___x_3440_;
goto v___jp_3430_;
}
}
else
{
lean_object* v___x_3441_; 
lean_inc_ref(v_value_3410_);
v___x_3441_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_value_3410_, v_snd_3437_);
v___y_3431_ = v___x_3441_;
goto v___jp_3430_;
}
}
else
{
lean_dec_ref(v___f_3375_);
v_fst_3413_ = v_fst_3436_;
v_snd_3414_ = v_snd_3437_;
goto v___jp_3412_;
}
}
v___jp_3442_:
{
lean_object* v_fst_3444_; lean_object* v_snd_3445_; uint8_t v___x_3446_; 
v_fst_3444_ = lean_ctor_get(v___y_3443_, 0);
lean_inc(v_fst_3444_);
v_snd_3445_ = lean_ctor_get(v___y_3443_, 1);
lean_inc(v_snd_3445_);
lean_dec_ref(v___y_3443_);
v___x_3446_ = lean_unbox(v_fst_3444_);
lean_dec(v_fst_3444_);
v_fst_3436_ = v___x_3446_;
v_snd_3437_ = v_snd_3445_;
goto v___jp_3435_;
}
}
else
{
lean_object* v_type_3454_; lean_object* v___x_3455_; uint8_t v_fst_3457_; lean_object* v_mctx_3458_; lean_object* v___y_3474_; lean_object* v_mctx_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v_type_3454_ = lean_ctor_get(v_val_3369_, 3);
v___x_3455_ = lean_st_ref_get(v___y_3351_);
v_mctx_3479_ = lean_ctor_get(v___x_3455_, 0);
lean_inc_ref_n(v_mctx_3479_, 2);
lean_dec(v___x_3455_);
v___x_3480_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v_mctx_3479_);
v___x_3482_ = l_Lean_Expr_hasFVar(v_type_3454_);
if (v___x_3482_ == 0)
{
uint8_t v___x_3483_; 
v___x_3483_ = l_Lean_Expr_hasMVar(v_type_3454_);
if (v___x_3483_ == 0)
{
lean_dec_ref_known(v___x_3481_, 2);
lean_dec_ref(v___f_3375_);
v_fst_3457_ = v___x_3483_;
v_mctx_3458_ = v_mctx_3479_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3484_; 
lean_dec_ref(v_mctx_3479_);
lean_inc_ref(v_type_3454_);
v___x_3484_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3454_, v___x_3481_);
v___y_3474_ = v___x_3484_;
goto v___jp_3473_;
}
}
else
{
lean_object* v___x_3485_; 
lean_dec_ref(v_mctx_3479_);
lean_inc_ref(v_type_3454_);
v___x_3485_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3375_, v___f_3374_, v_type_3454_, v___x_3481_);
v___y_3474_ = v___x_3485_;
goto v___jp_3473_;
}
v___jp_3456_:
{
lean_object* v___x_3459_; lean_object* v_cache_3460_; lean_object* v_zetaDeltaFVarIds_3461_; lean_object* v_postponed_3462_; lean_object* v_diag_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3471_; 
v___x_3459_ = lean_st_ref_take(v___y_3351_);
v_cache_3460_ = lean_ctor_get(v___x_3459_, 1);
v_zetaDeltaFVarIds_3461_ = lean_ctor_get(v___x_3459_, 2);
v_postponed_3462_ = lean_ctor_get(v___x_3459_, 3);
v_diag_3463_ = lean_ctor_get(v___x_3459_, 4);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3472_);
v___x_3465_ = v___x_3459_;
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_diag_3463_);
lean_inc(v_postponed_3462_);
lean_inc(v_zetaDeltaFVarIds_3461_);
lean_inc(v_cache_3460_);
lean_dec(v___x_3459_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_mctx_3458_);
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_mctx_3458_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_cache_3460_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_zetaDeltaFVarIds_3461_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_postponed_3462_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_diag_3463_);
v___x_3468_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_st_ref_put(v___y_3351_, v___x_3468_);
v_a_3371_ = v_fst_3457_;
goto v___jp_3370_;
}
}
}
v___jp_3473_:
{
lean_object* v_snd_3475_; lean_object* v_fst_3476_; lean_object* v_mctx_3477_; uint8_t v___x_3478_; 
v_snd_3475_ = lean_ctor_get(v___y_3474_, 1);
lean_inc(v_snd_3475_);
v_fst_3476_ = lean_ctor_get(v___y_3474_, 0);
lean_inc(v_fst_3476_);
lean_dec_ref(v___y_3474_);
v_mctx_3477_ = lean_ctor_get(v_snd_3475_, 1);
lean_inc_ref(v_mctx_3477_);
lean_dec(v_snd_3475_);
v___x_3478_ = lean_unbox(v_fst_3476_);
lean_dec(v_fst_3476_);
v_fst_3457_ = v___x_3478_;
v_mctx_3458_ = v_mctx_3477_;
goto v___jp_3456_;
}
}
}
v___jp_3370_:
{
if (v_a_3371_ == 0)
{
v_a_3361_ = v_snd_3355_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = l_Lean_LocalDecl_fvarId(v_val_3369_);
v___x_3373_ = lean_array_push(v_snd_3355_, v___x_3372_);
v_a_3361_ = v___x_3373_;
goto v___jp_3360_;
}
}
}
v___jp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 1, v_a_3361_);
lean_ctor_set(v___x_3357_, 0, v___x_3359_);
v___x_3363_ = v___x_3357_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_a_3361_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
size_t v___x_3364_; size_t v___x_3365_; 
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = lean_usize_add(v_i_3349_, v___x_3364_);
v_i_3349_ = v___x_3365_;
v_b_3350_ = v___x_3363_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3488_, lean_object* v_sz_3489_, lean_object* v_i_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
size_t v_sz_boxed_3494_; size_t v_i_boxed_3495_; lean_object* v_res_3496_; 
v_sz_boxed_3494_ = lean_unbox_usize(v_sz_3489_);
lean_dec(v_sz_3489_);
v_i_boxed_3495_ = lean_unbox_usize(v_i_3490_);
lean_dec(v_i_3490_);
v_res_3496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3488_, v_sz_boxed_3494_, v_i_boxed_3495_, v_b_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v_as_3488_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3497_, size_t v_sz_3498_, size_t v_i_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_usize_dec_lt(v_i_3499_, v_sz_3498_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3507_, 0, v_b_3500_);
return v___x_3507_;
}
else
{
lean_object* v_snd_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3639_; 
v_snd_3508_ = lean_ctor_get(v_b_3500_, 1);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_b_3500_);
if (v_isSharedCheck_3639_ == 0)
{
lean_object* v_unused_3640_; 
v_unused_3640_ = lean_ctor_get(v_b_3500_, 0);
lean_dec(v_unused_3640_);
v___x_3510_ = v_b_3500_;
v_isShared_3511_ = v_isSharedCheck_3639_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_snd_3508_);
lean_dec(v_b_3500_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3639_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v_a_3514_; lean_object* v_a_3521_; 
v___x_3512_ = lean_box(0);
v_a_3521_ = lean_array_uget_borrowed(v_as_3497_, v_i_3499_);
if (lean_obj_tag(v_a_3521_) == 0)
{
v_a_3514_ = v_snd_3508_;
goto v___jp_3513_;
}
else
{
lean_object* v_val_3522_; uint8_t v_a_3524_; lean_object* v___f_3527_; lean_object* v___f_3528_; 
v_val_3522_ = lean_ctor_get(v_a_3521_, 0);
v___f_3527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3508_);
v___f_3528_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3528_, 0, v_snd_3508_);
if (lean_obj_tag(v_val_3522_) == 0)
{
lean_object* v_type_3529_; lean_object* v___x_3530_; uint8_t v_fst_3532_; lean_object* v_mctx_3533_; lean_object* v___y_3549_; lean_object* v_mctx_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v_type_3529_ = lean_ctor_get(v_val_3522_, 3);
v___x_3530_ = lean_st_ref_get(v___y_3502_);
v_mctx_3554_ = lean_ctor_get(v___x_3530_, 0);
lean_inc_ref_n(v_mctx_3554_, 2);
lean_dec(v___x_3530_);
v___x_3555_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
lean_ctor_set(v___x_3556_, 1, v_mctx_3554_);
v___x_3557_ = l_Lean_Expr_hasFVar(v_type_3529_);
if (v___x_3557_ == 0)
{
uint8_t v___x_3558_; 
v___x_3558_ = l_Lean_Expr_hasMVar(v_type_3529_);
if (v___x_3558_ == 0)
{
lean_dec_ref_known(v___x_3556_, 2);
lean_dec_ref(v___f_3528_);
v_fst_3532_ = v___x_3558_;
v_mctx_3533_ = v_mctx_3554_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3559_; 
lean_dec_ref(v_mctx_3554_);
lean_inc_ref(v_type_3529_);
v___x_3559_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3529_, v___x_3556_);
v___y_3549_ = v___x_3559_;
goto v___jp_3548_;
}
}
else
{
lean_object* v___x_3560_; 
lean_dec_ref(v_mctx_3554_);
lean_inc_ref(v_type_3529_);
v___x_3560_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3529_, v___x_3556_);
v___y_3549_ = v___x_3560_;
goto v___jp_3548_;
}
v___jp_3531_:
{
lean_object* v___x_3534_; lean_object* v_cache_3535_; lean_object* v_zetaDeltaFVarIds_3536_; lean_object* v_postponed_3537_; lean_object* v_diag_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3546_; 
v___x_3534_ = lean_st_ref_take(v___y_3502_);
v_cache_3535_ = lean_ctor_get(v___x_3534_, 1);
v_zetaDeltaFVarIds_3536_ = lean_ctor_get(v___x_3534_, 2);
v_postponed_3537_ = lean_ctor_get(v___x_3534_, 3);
v_diag_3538_ = lean_ctor_get(v___x_3534_, 4);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; 
v_unused_3547_ = lean_ctor_get(v___x_3534_, 0);
lean_dec(v_unused_3547_);
v___x_3540_ = v___x_3534_;
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_diag_3538_);
lean_inc(v_postponed_3537_);
lean_inc(v_zetaDeltaFVarIds_3536_);
lean_inc(v_cache_3535_);
lean_dec(v___x_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v_mctx_3533_);
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_mctx_3533_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_cache_3535_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_zetaDeltaFVarIds_3536_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_postponed_3537_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v_diag_3538_);
v___x_3543_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_st_ref_put(v___y_3502_, v___x_3543_);
v_a_3524_ = v_fst_3532_;
goto v___jp_3523_;
}
}
}
v___jp_3548_:
{
lean_object* v_snd_3550_; lean_object* v_fst_3551_; lean_object* v_mctx_3552_; uint8_t v___x_3553_; 
v_snd_3550_ = lean_ctor_get(v___y_3549_, 1);
lean_inc(v_snd_3550_);
v_fst_3551_ = lean_ctor_get(v___y_3549_, 0);
lean_inc(v_fst_3551_);
lean_dec_ref(v___y_3549_);
v_mctx_3552_ = lean_ctor_get(v_snd_3550_, 1);
lean_inc_ref(v_mctx_3552_);
lean_dec(v_snd_3550_);
v___x_3553_ = lean_unbox(v_fst_3551_);
lean_dec(v_fst_3551_);
v_fst_3532_ = v___x_3553_;
v_mctx_3533_ = v_mctx_3552_;
goto v___jp_3531_;
}
}
else
{
uint8_t v_nondep_3561_; 
v_nondep_3561_ = lean_ctor_get_uint8(v_val_3522_, sizeof(void*)*5);
if (v_nondep_3561_ == 0)
{
lean_object* v_type_3562_; lean_object* v_value_3563_; lean_object* v___x_3564_; uint8_t v_fst_3566_; lean_object* v_snd_3567_; lean_object* v___y_3584_; uint8_t v_fst_3589_; lean_object* v_snd_3590_; lean_object* v___y_3596_; lean_object* v_mctx_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; 
v_type_3562_ = lean_ctor_get(v_val_3522_, 3);
v_value_3563_ = lean_ctor_get(v_val_3522_, 4);
v___x_3564_ = lean_st_ref_get(v___y_3502_);
v_mctx_3600_ = lean_ctor_get(v___x_3564_, 0);
lean_inc_ref(v_mctx_3600_);
lean_dec(v___x_3564_);
v___x_3601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v_mctx_3600_);
v___x_3603_ = l_Lean_Expr_hasFVar(v_type_3562_);
if (v___x_3603_ == 0)
{
uint8_t v___x_3604_; 
v___x_3604_ = l_Lean_Expr_hasMVar(v_type_3562_);
if (v___x_3604_ == 0)
{
v_fst_3589_ = v___x_3604_;
v_snd_3590_ = v___x_3602_;
goto v___jp_3588_;
}
else
{
lean_object* v___x_3605_; 
lean_inc_ref(v_type_3562_);
lean_inc_ref(v___f_3528_);
v___x_3605_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3562_, v___x_3602_);
v___y_3596_ = v___x_3605_;
goto v___jp_3595_;
}
}
else
{
lean_object* v___x_3606_; 
lean_inc_ref(v_type_3562_);
lean_inc_ref(v___f_3528_);
v___x_3606_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3562_, v___x_3602_);
v___y_3596_ = v___x_3606_;
goto v___jp_3595_;
}
v___jp_3565_:
{
lean_object* v_mctx_3568_; lean_object* v___x_3569_; lean_object* v_cache_3570_; lean_object* v_zetaDeltaFVarIds_3571_; lean_object* v_postponed_3572_; lean_object* v_diag_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3581_; 
v_mctx_3568_ = lean_ctor_get(v_snd_3567_, 1);
lean_inc_ref(v_mctx_3568_);
lean_dec_ref(v_snd_3567_);
v___x_3569_ = lean_st_ref_take(v___y_3502_);
v_cache_3570_ = lean_ctor_get(v___x_3569_, 1);
v_zetaDeltaFVarIds_3571_ = lean_ctor_get(v___x_3569_, 2);
v_postponed_3572_ = lean_ctor_get(v___x_3569_, 3);
v_diag_3573_ = lean_ctor_get(v___x_3569_, 4);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3569_, 0);
lean_dec(v_unused_3582_);
v___x_3575_ = v___x_3569_;
v_isShared_3576_ = v_isSharedCheck_3581_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_diag_3573_);
lean_inc(v_postponed_3572_);
lean_inc(v_zetaDeltaFVarIds_3571_);
lean_inc(v_cache_3570_);
lean_dec(v___x_3569_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3581_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v_mctx_3568_);
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_mctx_3568_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_cache_3570_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_zetaDeltaFVarIds_3571_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_postponed_3572_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_diag_3573_);
v___x_3578_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; 
v___x_3579_ = lean_st_ref_put(v___y_3502_, v___x_3578_);
v_a_3524_ = v_fst_3566_;
goto v___jp_3523_;
}
}
}
v___jp_3583_:
{
lean_object* v_fst_3585_; lean_object* v_snd_3586_; uint8_t v___x_3587_; 
v_fst_3585_ = lean_ctor_get(v___y_3584_, 0);
lean_inc(v_fst_3585_);
v_snd_3586_ = lean_ctor_get(v___y_3584_, 1);
lean_inc(v_snd_3586_);
lean_dec_ref(v___y_3584_);
v___x_3587_ = lean_unbox(v_fst_3585_);
lean_dec(v_fst_3585_);
v_fst_3566_ = v___x_3587_;
v_snd_3567_ = v_snd_3586_;
goto v___jp_3565_;
}
v___jp_3588_:
{
if (v_fst_3589_ == 0)
{
uint8_t v___x_3591_; 
v___x_3591_ = l_Lean_Expr_hasFVar(v_value_3563_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Lean_Expr_hasMVar(v_value_3563_);
if (v___x_3592_ == 0)
{
lean_dec_ref(v___f_3528_);
v_fst_3566_ = v___x_3592_;
v_snd_3567_ = v_snd_3590_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3593_; 
lean_inc_ref(v_value_3563_);
v___x_3593_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_value_3563_, v_snd_3590_);
v___y_3584_ = v___x_3593_;
goto v___jp_3583_;
}
}
else
{
lean_object* v___x_3594_; 
lean_inc_ref(v_value_3563_);
v___x_3594_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_value_3563_, v_snd_3590_);
v___y_3584_ = v___x_3594_;
goto v___jp_3583_;
}
}
else
{
lean_dec_ref(v___f_3528_);
v_fst_3566_ = v_fst_3589_;
v_snd_3567_ = v_snd_3590_;
goto v___jp_3565_;
}
}
v___jp_3595_:
{
lean_object* v_fst_3597_; lean_object* v_snd_3598_; uint8_t v___x_3599_; 
v_fst_3597_ = lean_ctor_get(v___y_3596_, 0);
lean_inc(v_fst_3597_);
v_snd_3598_ = lean_ctor_get(v___y_3596_, 1);
lean_inc(v_snd_3598_);
lean_dec_ref(v___y_3596_);
v___x_3599_ = lean_unbox(v_fst_3597_);
lean_dec(v_fst_3597_);
v_fst_3589_ = v___x_3599_;
v_snd_3590_ = v_snd_3598_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_type_3607_; lean_object* v___x_3608_; uint8_t v_fst_3610_; lean_object* v_mctx_3611_; lean_object* v___y_3627_; lean_object* v_mctx_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v_type_3607_ = lean_ctor_get(v_val_3522_, 3);
v___x_3608_ = lean_st_ref_get(v___y_3502_);
v_mctx_3632_ = lean_ctor_get(v___x_3608_, 0);
lean_inc_ref_n(v_mctx_3632_, 2);
lean_dec(v___x_3608_);
v___x_3633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_mctx_3632_);
v___x_3635_ = l_Lean_Expr_hasFVar(v_type_3607_);
if (v___x_3635_ == 0)
{
uint8_t v___x_3636_; 
v___x_3636_ = l_Lean_Expr_hasMVar(v_type_3607_);
if (v___x_3636_ == 0)
{
lean_dec_ref_known(v___x_3634_, 2);
lean_dec_ref(v___f_3528_);
v_fst_3610_ = v___x_3636_;
v_mctx_3611_ = v_mctx_3632_;
goto v___jp_3609_;
}
else
{
lean_object* v___x_3637_; 
lean_dec_ref(v_mctx_3632_);
lean_inc_ref(v_type_3607_);
v___x_3637_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3607_, v___x_3634_);
v___y_3627_ = v___x_3637_;
goto v___jp_3626_;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec_ref(v_mctx_3632_);
lean_inc_ref(v_type_3607_);
v___x_3638_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3528_, v___f_3527_, v_type_3607_, v___x_3634_);
v___y_3627_ = v___x_3638_;
goto v___jp_3626_;
}
v___jp_3609_:
{
lean_object* v___x_3612_; lean_object* v_cache_3613_; lean_object* v_zetaDeltaFVarIds_3614_; lean_object* v_postponed_3615_; lean_object* v_diag_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3624_; 
v___x_3612_ = lean_st_ref_take(v___y_3502_);
v_cache_3613_ = lean_ctor_get(v___x_3612_, 1);
v_zetaDeltaFVarIds_3614_ = lean_ctor_get(v___x_3612_, 2);
v_postponed_3615_ = lean_ctor_get(v___x_3612_, 3);
v_diag_3616_ = lean_ctor_get(v___x_3612_, 4);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v___x_3612_, 0);
lean_dec(v_unused_3625_);
v___x_3618_ = v___x_3612_;
v_isShared_3619_ = v_isSharedCheck_3624_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_diag_3616_);
lean_inc(v_postponed_3615_);
lean_inc(v_zetaDeltaFVarIds_3614_);
lean_inc(v_cache_3613_);
lean_dec(v___x_3612_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3624_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v_mctx_3611_);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_mctx_3611_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_cache_3613_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_zetaDeltaFVarIds_3614_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_postponed_3615_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v_diag_3616_);
v___x_3621_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_st_ref_put(v___y_3502_, v___x_3621_);
v_a_3524_ = v_fst_3610_;
goto v___jp_3523_;
}
}
}
v___jp_3626_:
{
lean_object* v_snd_3628_; lean_object* v_fst_3629_; lean_object* v_mctx_3630_; uint8_t v___x_3631_; 
v_snd_3628_ = lean_ctor_get(v___y_3627_, 1);
lean_inc(v_snd_3628_);
v_fst_3629_ = lean_ctor_get(v___y_3627_, 0);
lean_inc(v_fst_3629_);
lean_dec_ref(v___y_3627_);
v_mctx_3630_ = lean_ctor_get(v_snd_3628_, 1);
lean_inc_ref(v_mctx_3630_);
lean_dec(v_snd_3628_);
v___x_3631_ = lean_unbox(v_fst_3629_);
lean_dec(v_fst_3629_);
v_fst_3610_ = v___x_3631_;
v_mctx_3611_ = v_mctx_3630_;
goto v___jp_3609_;
}
}
}
v___jp_3523_:
{
if (v_a_3524_ == 0)
{
v_a_3514_ = v_snd_3508_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = l_Lean_LocalDecl_fvarId(v_val_3522_);
v___x_3526_ = lean_array_push(v_snd_3508_, v___x_3525_);
v_a_3514_ = v___x_3526_;
goto v___jp_3513_;
}
}
}
v___jp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v_a_3514_);
lean_ctor_set(v___x_3510_, 0, v___x_3512_);
v___x_3516_ = v___x_3510_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_a_3514_);
v___x_3516_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
size_t v___x_3517_; size_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = ((size_t)1ULL);
v___x_3518_ = lean_usize_add(v_i_3499_, v___x_3517_);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3497_, v_sz_3498_, v___x_3518_, v___x_3516_, v___y_3502_);
return v___x_3519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
size_t v_sz_boxed_3650_; size_t v_i_boxed_3651_; lean_object* v_res_3652_; 
v_sz_boxed_3650_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3651_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3641_, v_sz_boxed_3650_, v_i_boxed_3651_, v_b_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_as_3641_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3653_, lean_object* v_n_3654_, lean_object* v_b_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
if (lean_obj_tag(v_n_3654_) == 0)
{
lean_object* v_cs_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; size_t v_sz_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v_cs_3661_ = lean_ctor_get(v_n_3654_, 0);
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v_b_3655_);
v_sz_3664_ = lean_array_size(v_cs_3661_);
v___x_3665_ = ((size_t)0ULL);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3653_, v_cs_3661_, v_sz_3664_, v___x_3665_, v___x_3663_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3681_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_fst_3671_; 
v_fst_3671_ = lean_ctor_get(v_a_3667_, 0);
if (lean_obj_tag(v_fst_3671_) == 0)
{
lean_object* v_snd_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v_snd_3672_ = lean_ctor_get(v_a_3667_, 1);
lean_inc(v_snd_3672_);
lean_dec(v_a_3667_);
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_snd_3672_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3673_);
v___x_3675_ = v___x_3669_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
else
{
lean_object* v_val_3677_; lean_object* v___x_3679_; 
lean_inc_ref(v_fst_3671_);
lean_dec(v_a_3667_);
v_val_3677_ = lean_ctor_get(v_fst_3671_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_fst_3671_, 1);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_val_3677_);
v___x_3679_ = v___x_3669_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_val_3677_);
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
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3682_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3666_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3666_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v_vs_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; size_t v_sz_3693_; size_t v___x_3694_; lean_object* v___x_3695_; 
v_vs_3690_ = lean_ctor_get(v_n_3654_, 0);
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v_b_3655_);
v_sz_3693_ = lean_array_size(v_vs_3690_);
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3690_, v_sz_3693_, v___x_3694_, v___x_3692_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3710_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3710_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3710_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v_fst_3700_; 
v_fst_3700_ = lean_ctor_get(v_a_3696_, 0);
if (lean_obj_tag(v_fst_3700_) == 0)
{
lean_object* v_snd_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v_snd_3701_ = lean_ctor_get(v_a_3696_, 1);
lean_inc(v_snd_3701_);
lean_dec(v_a_3696_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_snd_3701_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3702_);
v___x_3704_ = v___x_3698_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3708_; 
lean_inc_ref(v_fst_3700_);
lean_dec(v_a_3696_);
v_val_3706_ = lean_ctor_get(v_fst_3700_, 0);
lean_inc(v_val_3706_);
lean_dec_ref_known(v_fst_3700_, 1);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v_val_3706_);
v___x_3708_ = v___x_3698_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_val_3706_);
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
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_a_3711_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3695_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3695_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3719_, lean_object* v_as_3720_, size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_b_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_b_3723_);
return v___x_3730_;
}
else
{
lean_object* v_snd_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3765_; 
v_snd_3731_ = lean_ctor_get(v_b_3723_, 1);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_b_3723_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v_b_3723_, 0);
lean_dec(v_unused_3766_);
v___x_3733_ = v_b_3723_;
v_isShared_3734_ = v_isSharedCheck_3765_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_snd_3731_);
lean_dec(v_b_3723_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3765_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_a_3735_; lean_object* v___x_3736_; 
v_a_3735_ = lean_array_uget_borrowed(v_as_3720_, v_i_3722_);
lean_inc(v_snd_3731_);
v___x_3736_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3719_, v_a_3735_, v_snd_3731_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3756_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3756_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3756_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
if (lean_obj_tag(v_a_3737_) == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3737_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3741_);
v___x_3743_ = v___x_3733_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_snd_3731_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3743_);
v___x_3745_ = v___x_3739_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_del_object(v___x_3739_);
lean_dec(v_snd_3731_);
v_a_3748_ = lean_ctor_get(v_a_3737_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v_a_3737_, 1);
v___x_3749_ = lean_box(0);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v_a_3748_);
lean_ctor_set(v___x_3733_, 0, v___x_3749_);
v___x_3751_ = v___x_3733_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_a_3748_);
v___x_3751_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
size_t v___x_3752_; size_t v___x_3753_; 
v___x_3752_ = ((size_t)1ULL);
v___x_3753_ = lean_usize_add(v_i_3722_, v___x_3752_);
v_i_3722_ = v___x_3753_;
v_b_3723_ = v___x_3751_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_del_object(v___x_3733_);
lean_dec(v_snd_3731_);
v_a_3757_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3736_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3736_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3767_, lean_object* v_as_3768_, lean_object* v_sz_3769_, lean_object* v_i_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
size_t v_sz_boxed_3777_; size_t v_i_boxed_3778_; lean_object* v_res_3779_; 
v_sz_boxed_3777_ = lean_unbox_usize(v_sz_3769_);
lean_dec(v_sz_3769_);
v_i_boxed_3778_ = lean_unbox_usize(v_i_3770_);
lean_dec(v_i_3770_);
v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3767_, v_as_3768_, v_sz_boxed_3777_, v_i_boxed_3778_, v_b_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec_ref(v_as_3768_);
lean_dec_ref(v_init_3767_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3780_, lean_object* v_n_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3780_, v_n_3781_, v_b_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_n_3781_);
lean_dec_ref(v_init_3780_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3789_, size_t v_sz_3790_, size_t v_i_3791_, lean_object* v_b_3792_, lean_object* v___y_3793_){
_start:
{
uint8_t v___x_3795_; 
v___x_3795_ = lean_usize_dec_lt(v_i_3791_, v_sz_3790_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_b_3792_);
return v___x_3796_;
}
else
{
lean_object* v_snd_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3928_; 
v_snd_3797_ = lean_ctor_get(v_b_3792_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_b_3792_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_b_3792_, 0);
lean_dec(v_unused_3929_);
v___x_3799_ = v_b_3792_;
v_isShared_3800_ = v_isSharedCheck_3928_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_snd_3797_);
lean_dec(v_b_3792_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3928_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v_a_3803_; lean_object* v_a_3810_; 
v___x_3801_ = lean_box(0);
v_a_3810_ = lean_array_uget_borrowed(v_as_3789_, v_i_3791_);
if (lean_obj_tag(v_a_3810_) == 0)
{
v_a_3803_ = v_snd_3797_;
goto v___jp_3802_;
}
else
{
lean_object* v_val_3811_; uint8_t v_a_3813_; lean_object* v___f_3816_; lean_object* v___f_3817_; 
v_val_3811_ = lean_ctor_get(v_a_3810_, 0);
v___f_3816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3797_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3817_, 0, v_snd_3797_);
if (lean_obj_tag(v_val_3811_) == 0)
{
lean_object* v_type_3818_; lean_object* v___x_3819_; uint8_t v_fst_3821_; lean_object* v_mctx_3822_; lean_object* v___y_3838_; lean_object* v_mctx_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_type_3818_ = lean_ctor_get(v_val_3811_, 3);
v___x_3819_ = lean_st_ref_get(v___y_3793_);
v_mctx_3843_ = lean_ctor_get(v___x_3819_, 0);
lean_inc_ref_n(v_mctx_3843_, 2);
lean_dec(v___x_3819_);
v___x_3844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v_mctx_3843_);
v___x_3846_ = l_Lean_Expr_hasFVar(v_type_3818_);
if (v___x_3846_ == 0)
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Lean_Expr_hasMVar(v_type_3818_);
if (v___x_3847_ == 0)
{
lean_dec_ref_known(v___x_3845_, 2);
lean_dec_ref(v___f_3817_);
v_fst_3821_ = v___x_3847_;
v_mctx_3822_ = v_mctx_3843_;
goto v___jp_3820_;
}
else
{
lean_object* v___x_3848_; 
lean_dec_ref(v_mctx_3843_);
lean_inc_ref(v_type_3818_);
v___x_3848_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3818_, v___x_3845_);
v___y_3838_ = v___x_3848_;
goto v___jp_3837_;
}
}
else
{
lean_object* v___x_3849_; 
lean_dec_ref(v_mctx_3843_);
lean_inc_ref(v_type_3818_);
v___x_3849_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3818_, v___x_3845_);
v___y_3838_ = v___x_3849_;
goto v___jp_3837_;
}
v___jp_3820_:
{
lean_object* v___x_3823_; lean_object* v_cache_3824_; lean_object* v_zetaDeltaFVarIds_3825_; lean_object* v_postponed_3826_; lean_object* v_diag_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3835_; 
v___x_3823_ = lean_st_ref_take(v___y_3793_);
v_cache_3824_ = lean_ctor_get(v___x_3823_, 1);
v_zetaDeltaFVarIds_3825_ = lean_ctor_get(v___x_3823_, 2);
v_postponed_3826_ = lean_ctor_get(v___x_3823_, 3);
v_diag_3827_ = lean_ctor_get(v___x_3823_, 4);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v___x_3823_, 0);
lean_dec(v_unused_3836_);
v___x_3829_ = v___x_3823_;
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_diag_3827_);
lean_inc(v_postponed_3826_);
lean_inc(v_zetaDeltaFVarIds_3825_);
lean_inc(v_cache_3824_);
lean_dec(v___x_3823_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v_mctx_3822_);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_mctx_3822_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_cache_3824_);
lean_ctor_set(v_reuseFailAlloc_3834_, 2, v_zetaDeltaFVarIds_3825_);
lean_ctor_set(v_reuseFailAlloc_3834_, 3, v_postponed_3826_);
lean_ctor_set(v_reuseFailAlloc_3834_, 4, v_diag_3827_);
v___x_3832_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_st_ref_put(v___y_3793_, v___x_3832_);
v_a_3813_ = v_fst_3821_;
goto v___jp_3812_;
}
}
}
v___jp_3837_:
{
lean_object* v_snd_3839_; lean_object* v_fst_3840_; lean_object* v_mctx_3841_; uint8_t v___x_3842_; 
v_snd_3839_ = lean_ctor_get(v___y_3838_, 1);
lean_inc(v_snd_3839_);
v_fst_3840_ = lean_ctor_get(v___y_3838_, 0);
lean_inc(v_fst_3840_);
lean_dec_ref(v___y_3838_);
v_mctx_3841_ = lean_ctor_get(v_snd_3839_, 1);
lean_inc_ref(v_mctx_3841_);
lean_dec(v_snd_3839_);
v___x_3842_ = lean_unbox(v_fst_3840_);
lean_dec(v_fst_3840_);
v_fst_3821_ = v___x_3842_;
v_mctx_3822_ = v_mctx_3841_;
goto v___jp_3820_;
}
}
else
{
uint8_t v_nondep_3850_; 
v_nondep_3850_ = lean_ctor_get_uint8(v_val_3811_, sizeof(void*)*5);
if (v_nondep_3850_ == 0)
{
lean_object* v_type_3851_; lean_object* v_value_3852_; lean_object* v___x_3853_; uint8_t v_fst_3855_; lean_object* v_snd_3856_; lean_object* v___y_3873_; uint8_t v_fst_3878_; lean_object* v_snd_3879_; lean_object* v___y_3885_; lean_object* v_mctx_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
v_type_3851_ = lean_ctor_get(v_val_3811_, 3);
v_value_3852_ = lean_ctor_get(v_val_3811_, 4);
v___x_3853_ = lean_st_ref_get(v___y_3793_);
v_mctx_3889_ = lean_ctor_get(v___x_3853_, 0);
lean_inc_ref(v_mctx_3889_);
lean_dec(v___x_3853_);
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v_mctx_3889_);
v___x_3892_ = l_Lean_Expr_hasFVar(v_type_3851_);
if (v___x_3892_ == 0)
{
uint8_t v___x_3893_; 
v___x_3893_ = l_Lean_Expr_hasMVar(v_type_3851_);
if (v___x_3893_ == 0)
{
v_fst_3878_ = v___x_3893_;
v_snd_3879_ = v___x_3891_;
goto v___jp_3877_;
}
else
{
lean_object* v___x_3894_; 
lean_inc_ref(v_type_3851_);
lean_inc_ref(v___f_3817_);
v___x_3894_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3851_, v___x_3891_);
v___y_3885_ = v___x_3894_;
goto v___jp_3884_;
}
}
else
{
lean_object* v___x_3895_; 
lean_inc_ref(v_type_3851_);
lean_inc_ref(v___f_3817_);
v___x_3895_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3851_, v___x_3891_);
v___y_3885_ = v___x_3895_;
goto v___jp_3884_;
}
v___jp_3854_:
{
lean_object* v_mctx_3857_; lean_object* v___x_3858_; lean_object* v_cache_3859_; lean_object* v_zetaDeltaFVarIds_3860_; lean_object* v_postponed_3861_; lean_object* v_diag_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3870_; 
v_mctx_3857_ = lean_ctor_get(v_snd_3856_, 1);
lean_inc_ref(v_mctx_3857_);
lean_dec_ref(v_snd_3856_);
v___x_3858_ = lean_st_ref_take(v___y_3793_);
v_cache_3859_ = lean_ctor_get(v___x_3858_, 1);
v_zetaDeltaFVarIds_3860_ = lean_ctor_get(v___x_3858_, 2);
v_postponed_3861_ = lean_ctor_get(v___x_3858_, 3);
v_diag_3862_ = lean_ctor_get(v___x_3858_, 4);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; 
v_unused_3871_ = lean_ctor_get(v___x_3858_, 0);
lean_dec(v_unused_3871_);
v___x_3864_ = v___x_3858_;
v_isShared_3865_ = v_isSharedCheck_3870_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_diag_3862_);
lean_inc(v_postponed_3861_);
lean_inc(v_zetaDeltaFVarIds_3860_);
lean_inc(v_cache_3859_);
lean_dec(v___x_3858_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3870_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_mctx_3857_);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_mctx_3857_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_cache_3859_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_zetaDeltaFVarIds_3860_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_postponed_3861_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v_diag_3862_);
v___x_3867_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_st_ref_put(v___y_3793_, v___x_3867_);
v_a_3813_ = v_fst_3855_;
goto v___jp_3812_;
}
}
}
v___jp_3872_:
{
lean_object* v_fst_3874_; lean_object* v_snd_3875_; uint8_t v___x_3876_; 
v_fst_3874_ = lean_ctor_get(v___y_3873_, 0);
lean_inc(v_fst_3874_);
v_snd_3875_ = lean_ctor_get(v___y_3873_, 1);
lean_inc(v_snd_3875_);
lean_dec_ref(v___y_3873_);
v___x_3876_ = lean_unbox(v_fst_3874_);
lean_dec(v_fst_3874_);
v_fst_3855_ = v___x_3876_;
v_snd_3856_ = v_snd_3875_;
goto v___jp_3854_;
}
v___jp_3877_:
{
if (v_fst_3878_ == 0)
{
uint8_t v___x_3880_; 
v___x_3880_ = l_Lean_Expr_hasFVar(v_value_3852_);
if (v___x_3880_ == 0)
{
uint8_t v___x_3881_; 
v___x_3881_ = l_Lean_Expr_hasMVar(v_value_3852_);
if (v___x_3881_ == 0)
{
lean_dec_ref(v___f_3817_);
v_fst_3855_ = v___x_3881_;
v_snd_3856_ = v_snd_3879_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3882_; 
lean_inc_ref(v_value_3852_);
v___x_3882_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_value_3852_, v_snd_3879_);
v___y_3873_ = v___x_3882_;
goto v___jp_3872_;
}
}
else
{
lean_object* v___x_3883_; 
lean_inc_ref(v_value_3852_);
v___x_3883_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_value_3852_, v_snd_3879_);
v___y_3873_ = v___x_3883_;
goto v___jp_3872_;
}
}
else
{
lean_dec_ref(v___f_3817_);
v_fst_3855_ = v_fst_3878_;
v_snd_3856_ = v_snd_3879_;
goto v___jp_3854_;
}
}
v___jp_3884_:
{
lean_object* v_fst_3886_; lean_object* v_snd_3887_; uint8_t v___x_3888_; 
v_fst_3886_ = lean_ctor_get(v___y_3885_, 0);
lean_inc(v_fst_3886_);
v_snd_3887_ = lean_ctor_get(v___y_3885_, 1);
lean_inc(v_snd_3887_);
lean_dec_ref(v___y_3885_);
v___x_3888_ = lean_unbox(v_fst_3886_);
lean_dec(v_fst_3886_);
v_fst_3878_ = v___x_3888_;
v_snd_3879_ = v_snd_3887_;
goto v___jp_3877_;
}
}
else
{
lean_object* v_type_3896_; lean_object* v___x_3897_; uint8_t v_fst_3899_; lean_object* v_mctx_3900_; lean_object* v___y_3916_; lean_object* v_mctx_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_type_3896_ = lean_ctor_get(v_val_3811_, 3);
v___x_3897_ = lean_st_ref_get(v___y_3793_);
v_mctx_3921_ = lean_ctor_get(v___x_3897_, 0);
lean_inc_ref_n(v_mctx_3921_, 2);
lean_dec(v___x_3897_);
v___x_3922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v_mctx_3921_);
v___x_3924_ = l_Lean_Expr_hasFVar(v_type_3896_);
if (v___x_3924_ == 0)
{
uint8_t v___x_3925_; 
v___x_3925_ = l_Lean_Expr_hasMVar(v_type_3896_);
if (v___x_3925_ == 0)
{
lean_dec_ref_known(v___x_3923_, 2);
lean_dec_ref(v___f_3817_);
v_fst_3899_ = v___x_3925_;
v_mctx_3900_ = v_mctx_3921_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3926_; 
lean_dec_ref(v_mctx_3921_);
lean_inc_ref(v_type_3896_);
v___x_3926_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3896_, v___x_3923_);
v___y_3916_ = v___x_3926_;
goto v___jp_3915_;
}
}
else
{
lean_object* v___x_3927_; 
lean_dec_ref(v_mctx_3921_);
lean_inc_ref(v_type_3896_);
v___x_3927_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3817_, v___f_3816_, v_type_3896_, v___x_3923_);
v___y_3916_ = v___x_3927_;
goto v___jp_3915_;
}
v___jp_3898_:
{
lean_object* v___x_3901_; lean_object* v_cache_3902_; lean_object* v_zetaDeltaFVarIds_3903_; lean_object* v_postponed_3904_; lean_object* v_diag_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3913_; 
v___x_3901_ = lean_st_ref_take(v___y_3793_);
v_cache_3902_ = lean_ctor_get(v___x_3901_, 1);
v_zetaDeltaFVarIds_3903_ = lean_ctor_get(v___x_3901_, 2);
v_postponed_3904_ = lean_ctor_get(v___x_3901_, 3);
v_diag_3905_ = lean_ctor_get(v___x_3901_, 4);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v___x_3901_, 0);
lean_dec(v_unused_3914_);
v___x_3907_ = v___x_3901_;
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_diag_3905_);
lean_inc(v_postponed_3904_);
lean_inc(v_zetaDeltaFVarIds_3903_);
lean_inc(v_cache_3902_);
lean_dec(v___x_3901_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v_mctx_3900_);
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_mctx_3900_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_cache_3902_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_zetaDeltaFVarIds_3903_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_postponed_3904_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_diag_3905_);
v___x_3910_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_st_ref_put(v___y_3793_, v___x_3910_);
v_a_3813_ = v_fst_3899_;
goto v___jp_3812_;
}
}
}
v___jp_3915_:
{
lean_object* v_snd_3917_; lean_object* v_fst_3918_; lean_object* v_mctx_3919_; uint8_t v___x_3920_; 
v_snd_3917_ = lean_ctor_get(v___y_3916_, 1);
lean_inc(v_snd_3917_);
v_fst_3918_ = lean_ctor_get(v___y_3916_, 0);
lean_inc(v_fst_3918_);
lean_dec_ref(v___y_3916_);
v_mctx_3919_ = lean_ctor_get(v_snd_3917_, 1);
lean_inc_ref(v_mctx_3919_);
lean_dec(v_snd_3917_);
v___x_3920_ = lean_unbox(v_fst_3918_);
lean_dec(v_fst_3918_);
v_fst_3899_ = v___x_3920_;
v_mctx_3900_ = v_mctx_3919_;
goto v___jp_3898_;
}
}
}
v___jp_3812_:
{
if (v_a_3813_ == 0)
{
v_a_3803_ = v_snd_3797_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = l_Lean_LocalDecl_fvarId(v_val_3811_);
v___x_3815_ = lean_array_push(v_snd_3797_, v___x_3814_);
v_a_3803_ = v___x_3815_;
goto v___jp_3802_;
}
}
}
v___jp_3802_:
{
lean_object* v___x_3805_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 1, v_a_3803_);
lean_ctor_set(v___x_3799_, 0, v___x_3801_);
v___x_3805_ = v___x_3799_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_a_3803_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
size_t v___x_3806_; size_t v___x_3807_; 
v___x_3806_ = ((size_t)1ULL);
v___x_3807_ = lean_usize_add(v_i_3791_, v___x_3806_);
v_i_3791_ = v___x_3807_;
v_b_3792_ = v___x_3805_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3930_, lean_object* v_sz_3931_, lean_object* v_i_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
size_t v_sz_boxed_3936_; size_t v_i_boxed_3937_; lean_object* v_res_3938_; 
v_sz_boxed_3936_ = lean_unbox_usize(v_sz_3931_);
lean_dec(v_sz_3931_);
v_i_boxed_3937_ = lean_unbox_usize(v_i_3932_);
lean_dec(v_i_3932_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3930_, v_sz_boxed_3936_, v_i_boxed_3937_, v_b_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v_as_3930_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3939_, size_t v_sz_3940_, size_t v_i_3941_, lean_object* v_b_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_usize_dec_lt(v_i_3941_, v_sz_3940_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3942_);
return v___x_3949_;
}
else
{
lean_object* v_snd_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4081_; 
v_snd_3950_ = lean_ctor_get(v_b_3942_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_b_3942_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v_b_3942_, 0);
lean_dec(v_unused_4082_);
v___x_3952_ = v_b_3942_;
v_isShared_3953_ = v_isSharedCheck_4081_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_snd_3950_);
lean_dec(v_b_3942_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4081_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v_a_3956_; lean_object* v_a_3963_; 
v___x_3954_ = lean_box(0);
v_a_3963_ = lean_array_uget_borrowed(v_as_3939_, v_i_3941_);
if (lean_obj_tag(v_a_3963_) == 0)
{
v_a_3956_ = v_snd_3950_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_3964_; uint8_t v_a_3966_; lean_object* v___f_3969_; lean_object* v___f_3970_; 
v_val_3964_ = lean_ctor_get(v_a_3963_, 0);
v___f_3969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3950_);
v___f_3970_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3970_, 0, v_snd_3950_);
if (lean_obj_tag(v_val_3964_) == 0)
{
lean_object* v_type_3971_; lean_object* v___x_3972_; uint8_t v_fst_3974_; lean_object* v_mctx_3975_; lean_object* v___y_3991_; lean_object* v_mctx_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_type_3971_ = lean_ctor_get(v_val_3964_, 3);
v___x_3972_ = lean_st_ref_get(v___y_3944_);
v_mctx_3996_ = lean_ctor_get(v___x_3972_, 0);
lean_inc_ref_n(v_mctx_3996_, 2);
lean_dec(v___x_3972_);
v___x_3997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v_mctx_3996_);
v___x_3999_ = l_Lean_Expr_hasFVar(v_type_3971_);
if (v___x_3999_ == 0)
{
uint8_t v___x_4000_; 
v___x_4000_ = l_Lean_Expr_hasMVar(v_type_3971_);
if (v___x_4000_ == 0)
{
lean_dec_ref_known(v___x_3998_, 2);
lean_dec_ref(v___f_3970_);
v_fst_3974_ = v___x_4000_;
v_mctx_3975_ = v_mctx_3996_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_4001_; 
lean_dec_ref(v_mctx_3996_);
lean_inc_ref(v_type_3971_);
v___x_4001_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_3971_, v___x_3998_);
v___y_3991_ = v___x_4001_;
goto v___jp_3990_;
}
}
else
{
lean_object* v___x_4002_; 
lean_dec_ref(v_mctx_3996_);
lean_inc_ref(v_type_3971_);
v___x_4002_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_3971_, v___x_3998_);
v___y_3991_ = v___x_4002_;
goto v___jp_3990_;
}
v___jp_3973_:
{
lean_object* v___x_3976_; lean_object* v_cache_3977_; lean_object* v_zetaDeltaFVarIds_3978_; lean_object* v_postponed_3979_; lean_object* v_diag_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3988_; 
v___x_3976_ = lean_st_ref_take(v___y_3944_);
v_cache_3977_ = lean_ctor_get(v___x_3976_, 1);
v_zetaDeltaFVarIds_3978_ = lean_ctor_get(v___x_3976_, 2);
v_postponed_3979_ = lean_ctor_get(v___x_3976_, 3);
v_diag_3980_ = lean_ctor_get(v___x_3976_, 4);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3976_, 0);
lean_dec(v_unused_3989_);
v___x_3982_ = v___x_3976_;
v_isShared_3983_ = v_isSharedCheck_3988_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_diag_3980_);
lean_inc(v_postponed_3979_);
lean_inc(v_zetaDeltaFVarIds_3978_);
lean_inc(v_cache_3977_);
lean_dec(v___x_3976_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3988_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_mctx_3975_);
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_mctx_3975_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_cache_3977_);
lean_ctor_set(v_reuseFailAlloc_3987_, 2, v_zetaDeltaFVarIds_3978_);
lean_ctor_set(v_reuseFailAlloc_3987_, 3, v_postponed_3979_);
lean_ctor_set(v_reuseFailAlloc_3987_, 4, v_diag_3980_);
v___x_3985_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_st_ref_put(v___y_3944_, v___x_3985_);
v_a_3966_ = v_fst_3974_;
goto v___jp_3965_;
}
}
}
v___jp_3990_:
{
lean_object* v_snd_3992_; lean_object* v_fst_3993_; lean_object* v_mctx_3994_; uint8_t v___x_3995_; 
v_snd_3992_ = lean_ctor_get(v___y_3991_, 1);
lean_inc(v_snd_3992_);
v_fst_3993_ = lean_ctor_get(v___y_3991_, 0);
lean_inc(v_fst_3993_);
lean_dec_ref(v___y_3991_);
v_mctx_3994_ = lean_ctor_get(v_snd_3992_, 1);
lean_inc_ref(v_mctx_3994_);
lean_dec(v_snd_3992_);
v___x_3995_ = lean_unbox(v_fst_3993_);
lean_dec(v_fst_3993_);
v_fst_3974_ = v___x_3995_;
v_mctx_3975_ = v_mctx_3994_;
goto v___jp_3973_;
}
}
else
{
uint8_t v_nondep_4003_; 
v_nondep_4003_ = lean_ctor_get_uint8(v_val_3964_, sizeof(void*)*5);
if (v_nondep_4003_ == 0)
{
lean_object* v_type_4004_; lean_object* v_value_4005_; lean_object* v___x_4006_; uint8_t v_fst_4008_; lean_object* v_snd_4009_; lean_object* v___y_4026_; uint8_t v_fst_4031_; lean_object* v_snd_4032_; lean_object* v___y_4038_; lean_object* v_mctx_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v_type_4004_ = lean_ctor_get(v_val_3964_, 3);
v_value_4005_ = lean_ctor_get(v_val_3964_, 4);
v___x_4006_ = lean_st_ref_get(v___y_3944_);
v_mctx_4042_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_ref(v_mctx_4042_);
lean_dec(v___x_4006_);
v___x_4043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v_mctx_4042_);
v___x_4045_ = l_Lean_Expr_hasFVar(v_type_4004_);
if (v___x_4045_ == 0)
{
uint8_t v___x_4046_; 
v___x_4046_ = l_Lean_Expr_hasMVar(v_type_4004_);
if (v___x_4046_ == 0)
{
v_fst_4031_ = v___x_4046_;
v_snd_4032_ = v___x_4044_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4047_; 
lean_inc_ref(v_type_4004_);
lean_inc_ref(v___f_3970_);
v___x_4047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_4004_, v___x_4044_);
v___y_4038_ = v___x_4047_;
goto v___jp_4037_;
}
}
else
{
lean_object* v___x_4048_; 
lean_inc_ref(v_type_4004_);
lean_inc_ref(v___f_3970_);
v___x_4048_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_4004_, v___x_4044_);
v___y_4038_ = v___x_4048_;
goto v___jp_4037_;
}
v___jp_4007_:
{
lean_object* v_mctx_4010_; lean_object* v___x_4011_; lean_object* v_cache_4012_; lean_object* v_zetaDeltaFVarIds_4013_; lean_object* v_postponed_4014_; lean_object* v_diag_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4023_; 
v_mctx_4010_ = lean_ctor_get(v_snd_4009_, 1);
lean_inc_ref(v_mctx_4010_);
lean_dec_ref(v_snd_4009_);
v___x_4011_ = lean_st_ref_take(v___y_3944_);
v_cache_4012_ = lean_ctor_get(v___x_4011_, 1);
v_zetaDeltaFVarIds_4013_ = lean_ctor_get(v___x_4011_, 2);
v_postponed_4014_ = lean_ctor_get(v___x_4011_, 3);
v_diag_4015_ = lean_ctor_get(v___x_4011_, 4);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v___x_4011_, 0);
lean_dec(v_unused_4024_);
v___x_4017_ = v___x_4011_;
v_isShared_4018_ = v_isSharedCheck_4023_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_diag_4015_);
lean_inc(v_postponed_4014_);
lean_inc(v_zetaDeltaFVarIds_4013_);
lean_inc(v_cache_4012_);
lean_dec(v___x_4011_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4023_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v_mctx_4010_);
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_mctx_4010_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_cache_4012_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_zetaDeltaFVarIds_4013_);
lean_ctor_set(v_reuseFailAlloc_4022_, 3, v_postponed_4014_);
lean_ctor_set(v_reuseFailAlloc_4022_, 4, v_diag_4015_);
v___x_4020_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_st_ref_put(v___y_3944_, v___x_4020_);
v_a_3966_ = v_fst_4008_;
goto v___jp_3965_;
}
}
}
v___jp_4025_:
{
lean_object* v_fst_4027_; lean_object* v_snd_4028_; uint8_t v___x_4029_; 
v_fst_4027_ = lean_ctor_get(v___y_4026_, 0);
lean_inc(v_fst_4027_);
v_snd_4028_ = lean_ctor_get(v___y_4026_, 1);
lean_inc(v_snd_4028_);
lean_dec_ref(v___y_4026_);
v___x_4029_ = lean_unbox(v_fst_4027_);
lean_dec(v_fst_4027_);
v_fst_4008_ = v___x_4029_;
v_snd_4009_ = v_snd_4028_;
goto v___jp_4007_;
}
v___jp_4030_:
{
if (v_fst_4031_ == 0)
{
uint8_t v___x_4033_; 
v___x_4033_ = l_Lean_Expr_hasFVar(v_value_4005_);
if (v___x_4033_ == 0)
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Lean_Expr_hasMVar(v_value_4005_);
if (v___x_4034_ == 0)
{
lean_dec_ref(v___f_3970_);
v_fst_4008_ = v___x_4034_;
v_snd_4009_ = v_snd_4032_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4035_; 
lean_inc_ref(v_value_4005_);
v___x_4035_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_value_4005_, v_snd_4032_);
v___y_4026_ = v___x_4035_;
goto v___jp_4025_;
}
}
else
{
lean_object* v___x_4036_; 
lean_inc_ref(v_value_4005_);
v___x_4036_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_value_4005_, v_snd_4032_);
v___y_4026_ = v___x_4036_;
goto v___jp_4025_;
}
}
else
{
lean_dec_ref(v___f_3970_);
v_fst_4008_ = v_fst_4031_;
v_snd_4009_ = v_snd_4032_;
goto v___jp_4007_;
}
}
v___jp_4037_:
{
lean_object* v_fst_4039_; lean_object* v_snd_4040_; uint8_t v___x_4041_; 
v_fst_4039_ = lean_ctor_get(v___y_4038_, 0);
lean_inc(v_fst_4039_);
v_snd_4040_ = lean_ctor_get(v___y_4038_, 1);
lean_inc(v_snd_4040_);
lean_dec_ref(v___y_4038_);
v___x_4041_ = lean_unbox(v_fst_4039_);
lean_dec(v_fst_4039_);
v_fst_4031_ = v___x_4041_;
v_snd_4032_ = v_snd_4040_;
goto v___jp_4030_;
}
}
else
{
lean_object* v_type_4049_; lean_object* v___x_4050_; uint8_t v_fst_4052_; lean_object* v_mctx_4053_; lean_object* v___y_4069_; lean_object* v_mctx_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_type_4049_ = lean_ctor_get(v_val_3964_, 3);
v___x_4050_ = lean_st_ref_get(v___y_3944_);
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
lean_dec_ref(v___f_3970_);
v_fst_4052_ = v___x_4078_;
v_mctx_4053_ = v_mctx_4074_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4079_; 
lean_dec_ref(v_mctx_4074_);
lean_inc_ref(v_type_4049_);
v___x_4079_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_4049_, v___x_4076_);
v___y_4069_ = v___x_4079_;
goto v___jp_4068_;
}
}
else
{
lean_object* v___x_4080_; 
lean_dec_ref(v_mctx_4074_);
lean_inc_ref(v_type_4049_);
v___x_4080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3970_, v___f_3969_, v_type_4049_, v___x_4076_);
v___y_4069_ = v___x_4080_;
goto v___jp_4068_;
}
v___jp_4051_:
{
lean_object* v___x_4054_; lean_object* v_cache_4055_; lean_object* v_zetaDeltaFVarIds_4056_; lean_object* v_postponed_4057_; lean_object* v_diag_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4066_; 
v___x_4054_ = lean_st_ref_take(v___y_3944_);
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
v___x_4064_ = lean_st_ref_put(v___y_3944_, v___x_4063_);
v_a_3966_ = v_fst_4052_;
goto v___jp_3965_;
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
v___jp_3965_:
{
if (v_a_3966_ == 0)
{
v_a_3956_ = v_snd_3950_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = l_Lean_LocalDecl_fvarId(v_val_3964_);
v___x_3968_ = lean_array_push(v_snd_3950_, v___x_3967_);
v_a_3956_ = v___x_3968_;
goto v___jp_3955_;
}
}
}
v___jp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v_a_3956_);
lean_ctor_set(v___x_3952_, 0, v___x_3954_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_a_3956_);
v___x_3958_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = ((size_t)1ULL);
v___x_3960_ = lean_usize_add(v_i_3941_, v___x_3959_);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3939_, v_sz_3940_, v___x_3960_, v___x_3958_, v___y_3944_);
return v___x_3961_;
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
lean_object* v_a_4254_; lean_object* v_fst_4255_; lean_object* v_snd_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v_a_4254_ = lean_array_uget_borrowed(v_as_4241_, v_i_4243_);
v_fst_4255_ = lean_ctor_get(v_a_4254_, 0);
v_snd_4256_ = lean_ctor_get(v_a_4254_, 1);
lean_inc(v_snd_4256_);
v___x_4257_ = l_Lean_Meta_FVarSubst_get(v_fs_4240_, v_snd_4256_);
lean_inc(v_fst_4255_);
v___x_4258_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4255_, v___x_4257_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v___x_4259_; size_t v___x_4260_; size_t v___x_4261_; 
lean_dec_ref_known(v___x_4258_, 1);
v___x_4259_ = lean_box(0);
v___x_4260_ = ((size_t)1ULL);
v___x_4261_ = lean_usize_add(v_i_4243_, v___x_4260_);
v_i_4243_ = v___x_4261_;
v_b_4244_ = v___x_4259_;
goto _start;
}
else
{
return v___x_4258_;
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
size_t v_sz_boxed_4311_; size_t v___x_1633__boxed_4312_; lean_object* v_res_4313_; 
v_sz_boxed_4311_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v___x_1633__boxed_4312_ = lean_unbox_usize(v___x_4302_);
lean_dec(v___x_4302_);
v_res_4313_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4299_, v_toTag_4300_, v_sz_boxed_4311_, v___x_1633__boxed_4312_, v___x_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
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
uint8_t v___x_4433_; 
v___x_4433_ = lean_nat_dec_le(v___x_4430_, v___x_4430_);
if (v___x_4433_ == 0)
{
if (v___x_4432_ == 0)
{
lean_dec_ref(v___x_4428_);
v___y_4389_ = v___x_4431_;
goto v___jp_4388_;
}
else
{
size_t v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = lean_usize_of_nat(v___x_4430_);
v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4428_, v___x_4427_, v___x_4434_, v___x_4431_);
lean_dec_ref(v___x_4428_);
v___y_4389_ = v___x_4435_;
goto v___jp_4388_;
}
}
else
{
size_t v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = lean_usize_of_nat(v___x_4430_);
v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4428_, v___x_4427_, v___x_4436_, v___x_4431_);
lean_dec_ref(v___x_4428_);
v___y_4389_ = v___x_4437_;
goto v___jp_4388_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4438_, lean_object* v_g_4439_, lean_object* v_fs_4440_, lean_object* v_clears_4441_, lean_object* v_gs_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4438_, v_g_4439_, v_fs_4440_, v_clears_4441_, v_gs_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
return v_res_4450_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = lean_box(0);
v___x_4452_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
lean_ctor_set(v___x_4453_, 1, v___x_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4455_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; uint8_t v___x_4518_; 
v___x_4517_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4511_);
v___x_4518_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4511_);
v___x_4520_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4511_);
v___x_4522_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; uint8_t v___x_4524_; 
v___x_4523_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4511_);
v___x_4524_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4511_);
v___x_4526_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4511_);
v___x_4528_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4511_);
v___x_4530_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4511_);
v___x_4532_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; 
lean_dec(v_stx_4511_);
v___x_4533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4533_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = lean_unsigned_to_nat(1u);
v___x_4535_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4534_);
v___x_4536_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4535_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4545_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4541_, 0, v_stx_4511_);
lean_ctor_set(v___x_4541_, 1, v_a_4537_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4543_ = v___x_4539_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
else
{
lean_dec(v_stx_4511_);
return v___x_4536_;
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v_ps_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4546_ = lean_unsigned_to_nat(1u);
v___x_4547_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4546_);
v_ps_4548_ = l_Lean_Syntax_getArgs(v___x_4547_);
lean_dec(v___x_4547_);
v___x_4549_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4548_);
lean_dec_ref(v_ps_4548_);
v___x_4550_ = lean_array_to_list(v___x_4549_);
v___x_4551_ = lean_box(0);
v___x_4552_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4550_, v___x_4551_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4561_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4561_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4557_; lean_object* v___x_4559_; 
v___x_4557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4557_, 0, v_stx_4511_);
lean_ctor_set(v___x_4557_, 1, v_a_4553_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4557_);
v___x_4559_ = v___x_4555_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_stx_4511_);
v_a_4562_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4552_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4552_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_unsigned_to_nat(1u);
v___x_4571_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4570_);
v___x_4572_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4571_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4581_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4581_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4581_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4577_; lean_object* v___x_4579_; 
v___x_4577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4577_, 0, v_stx_4511_);
lean_ctor_set(v___x_4577_, 1, v_a_4573_);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4577_);
v___x_4579_ = v___x_4575_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
else
{
lean_dec(v_stx_4511_);
return v___x_4572_;
}
}
}
else
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_stx_4511_);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
}
else
{
lean_object* v___x_4584_; lean_object* v_h_4585_; 
v___x_4584_ = lean_unsigned_to_nat(0u);
v_h_4585_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4584_);
lean_dec(v_stx_4511_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4590_; uint8_t v___x_4591_; 
v___x_4590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4585_);
v___x_4591_ = l_Lean_Syntax_isOfKind(v_h_4585_, v___x_4590_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_dec(v_h_4585_);
v___x_4592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4592_;
}
else
{
goto v___jp_4586_;
}
}
else
{
goto v___jp_4586_;
}
v___jp_4586_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = l_Lean_TSyntax_getId(v_h_4585_);
v___x_4588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4588_, 0, v_h_4585_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4594_, 0, v_stx_4511_);
lean_ctor_set(v___x_4594_, 1, v___x_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_unsigned_to_nat(0u);
v___x_4597_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4596_);
if (v___x_4518_ == 0)
{
uint8_t v___x_4617_; 
lean_inc(v___x_4597_);
v___x_4617_ = l_Lean_Syntax_isOfKind(v___x_4597_, v___x_4517_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; 
lean_dec(v___x_4597_);
lean_dec(v_stx_4511_);
v___x_4618_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4618_;
}
else
{
goto v___jp_4598_;
}
}
else
{
goto v___jp_4598_;
}
v___jp_4598_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v___x_4599_ = lean_unsigned_to_nat(1u);
v___x_4600_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4599_);
v___x_4601_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4600_);
v___x_4602_ = l_Lean_Syntax_matchesNull(v___x_4600_, v___x_4601_);
if (v___x_4602_ == 0)
{
uint8_t v___x_4603_; 
lean_dec(v_stx_4511_);
v___x_4603_ = l_Lean_Syntax_matchesNull(v___x_4600_, v___x_4596_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
lean_dec(v___x_4597_);
v___x_4604_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4604_;
}
else
{
v_stx_4511_ = v___x_4597_;
goto _start;
}
}
else
{
lean_object* v___x_4606_; 
v___x_4606_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4597_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4616_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4616_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4616_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_t_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v_t_4611_ = l_Lean_Syntax_getArg(v___x_4600_, v___x_4599_);
lean_dec(v___x_4600_);
v___x_4612_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4612_, 0, v_stx_4511_);
lean_ctor_set(v___x_4612_, 1, v_a_4607_);
lean_ctor_set(v___x_4612_, 2, v_t_4611_);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4612_);
v___x_4614_ = v___x_4609_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
else
{
lean_dec(v___x_4600_);
lean_dec(v_stx_4511_);
return v___x_4606_;
}
}
}
}
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v_ps_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4619_);
v_ps_4621_ = l_Lean_Syntax_getArgs(v___x_4620_);
lean_dec(v___x_4620_);
v___x_4622_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4621_);
lean_dec_ref(v_ps_4621_);
v___x_4623_ = lean_array_to_list(v___x_4622_);
v___x_4624_ = lean_box(0);
v___x_4625_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4623_, v___x_4624_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4634_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4630_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4511_, v_a_4626_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4630_);
v___x_4632_ = v___x_4628_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec(v_stx_4511_);
v_a_4635_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4625_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4625_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4643_, lean_object* v_x_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
if (lean_obj_tag(v_x_4643_) == 0)
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = l_List_reverse___redArg(v_x_4644_);
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
return v___x_4651_;
}
else
{
lean_object* v_head_4652_; lean_object* v_tail_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4671_; 
v_head_4652_ = lean_ctor_get(v_x_4643_, 0);
v_tail_4653_ = lean_ctor_get(v_x_4643_, 1);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_x_4643_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4655_ = v_x_4643_;
v_isShared_4656_ = v_isSharedCheck_4671_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_tail_4653_);
lean_inc(v_head_4652_);
lean_dec(v_x_4643_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4671_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4652_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v___x_4657_, 1);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v_x_4644_);
lean_ctor_set(v___x_4655_, 0, v_a_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4658_);
lean_ctor_set(v_reuseFailAlloc_4662_, 1, v_x_4644_);
v___x_4660_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
v_x_4643_ = v_tail_4653_;
v_x_4644_ = v___x_4660_;
goto _start;
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_del_object(v___x_4655_);
lean_dec(v_tail_4653_);
lean_dec(v_x_4644_);
v_a_4663_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4657_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4657_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4672_, lean_object* v_x_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4672_, v_x_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4687_, lean_object* v_as_4688_, size_t v_sz_4689_, size_t v_i_4690_, lean_object* v_b_4691_){
_start:
{
lean_object* v_a_4694_; uint8_t v___x_4698_; 
v___x_4698_ = lean_usize_dec_lt(v_i_4690_, v_sz_4689_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; 
v___x_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4699_, 0, v_b_4691_);
return v___x_4699_;
}
else
{
lean_object* v_fst_4700_; lean_object* v_snd_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4723_; 
v_fst_4700_ = lean_ctor_get(v_b_4691_, 0);
v_snd_4701_ = lean_ctor_get(v_b_4691_, 1);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_b_4691_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4703_ = v_b_4691_;
v_isShared_4704_ = v_isSharedCheck_4723_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_snd_4701_);
lean_inc(v_fst_4700_);
lean_dec(v_b_4691_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4723_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v_a_4705_; lean_object* v_expr_4706_; lean_object* v_hName_x3f_4707_; lean_object* v___x_4708_; uint8_t v___y_4719_; uint8_t v___x_4722_; 
v_a_4705_ = lean_array_uget_borrowed(v_as_4688_, v_i_4690_);
v_expr_4706_ = lean_ctor_get(v_a_4705_, 0);
v_hName_x3f_4707_ = lean_ctor_get(v_a_4705_, 2);
v___x_4708_ = lean_box(0);
v___x_4722_ = l_Lean_Expr_isFVar(v_expr_4706_);
if (v___x_4722_ == 0)
{
v___y_4719_ = v___x_4722_;
goto v___jp_4718_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4707_) == 0)
{
v___y_4719_ = v___x_4722_;
goto v___jp_4718_;
}
else
{
goto v___jp_4709_;
}
}
v___jp_4709_:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4710_ = lean_array_get_borrowed(v___x_4708_, v_fst_4687_, v_snd_4701_);
lean_inc(v___x_4710_);
v___x_4711_ = l_Lean_mkFVar(v___x_4710_);
v___x_4712_ = lean_array_push(v_fst_4700_, v___x_4711_);
v___x_4713_ = lean_unsigned_to_nat(1u);
v___x_4714_ = lean_nat_add(v_snd_4701_, v___x_4713_);
lean_dec(v_snd_4701_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 1, v___x_4714_);
lean_ctor_set(v___x_4703_, 0, v___x_4712_);
v___x_4716_ = v___x_4703_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
v_a_4694_ = v___x_4716_;
goto v___jp_4693_;
}
}
v___jp_4718_:
{
if (v___y_4719_ == 0)
{
goto v___jp_4709_;
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_del_object(v___x_4703_);
lean_inc_ref(v_expr_4706_);
v___x_4720_ = lean_array_push(v_fst_4700_, v_expr_4706_);
v___x_4721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
lean_ctor_set(v___x_4721_, 1, v_snd_4701_);
v_a_4694_ = v___x_4721_;
goto v___jp_4693_;
}
}
}
}
v___jp_4693_:
{
size_t v___x_4695_; size_t v___x_4696_; 
v___x_4695_ = ((size_t)1ULL);
v___x_4696_ = lean_usize_add(v_i_4690_, v___x_4695_);
v_i_4690_ = v___x_4696_;
v_b_4691_ = v_a_4694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4724_, lean_object* v_as_4725_, lean_object* v_sz_4726_, lean_object* v_i_4727_, lean_object* v_b_4728_, lean_object* v___y_4729_){
_start:
{
size_t v_sz_boxed_4730_; size_t v_i_boxed_4731_; lean_object* v_res_4732_; 
v_sz_boxed_4730_ = lean_unbox_usize(v_sz_4726_);
lean_dec(v_sz_4726_);
v_i_boxed_4731_ = lean_unbox_usize(v_i_4727_);
lean_dec(v_i_4727_);
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4724_, v_as_4725_, v_sz_boxed_4730_, v_i_boxed_4731_, v_b_4728_);
lean_dec_ref(v_as_4725_);
lean_dec_ref(v_fst_4724_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4733_, size_t v_i_4734_, size_t v_stop_4735_, lean_object* v_b_4736_){
_start:
{
lean_object* v___y_4738_; uint8_t v___x_4742_; 
v___x_4742_ = lean_usize_dec_eq(v_i_4734_, v_stop_4735_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; uint8_t v___y_4745_; lean_object* v_expr_4747_; lean_object* v_hName_x3f_4748_; uint8_t v___x_4749_; 
v___x_4743_ = lean_array_uget_borrowed(v_as_4733_, v_i_4734_);
v_expr_4747_ = lean_ctor_get(v___x_4743_, 0);
v_hName_x3f_4748_ = lean_ctor_get(v___x_4743_, 2);
v___x_4749_ = l_Lean_Expr_isFVar(v_expr_4747_);
if (v___x_4749_ == 0)
{
v___y_4745_ = v___x_4749_;
goto v___jp_4744_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4748_) == 0)
{
v___y_4745_ = v___x_4749_;
goto v___jp_4744_;
}
else
{
lean_object* v___x_4750_; 
lean_inc(v___x_4743_);
v___x_4750_ = lean_array_push(v_b_4736_, v___x_4743_);
v___y_4738_ = v___x_4750_;
goto v___jp_4737_;
}
}
v___jp_4744_:
{
if (v___y_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_inc(v___x_4743_);
v___x_4746_ = lean_array_push(v_b_4736_, v___x_4743_);
v___y_4738_ = v___x_4746_;
goto v___jp_4737_;
}
else
{
v___y_4738_ = v_b_4736_;
goto v___jp_4737_;
}
}
}
else
{
return v_b_4736_;
}
v___jp_4737_:
{
size_t v___x_4739_; size_t v___x_4740_; 
v___x_4739_ = ((size_t)1ULL);
v___x_4740_ = lean_usize_add(v_i_4734_, v___x_4739_);
v_i_4734_ = v___x_4740_;
v_b_4736_ = v___y_4738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4751_, lean_object* v_i_4752_, lean_object* v_stop_4753_, lean_object* v_b_4754_){
_start:
{
size_t v_i_boxed_4755_; size_t v_stop_boxed_4756_; lean_object* v_res_4757_; 
v_i_boxed_4755_ = lean_unbox_usize(v_i_4752_);
lean_dec(v_i_4752_);
v_stop_boxed_4756_ = lean_unbox_usize(v_stop_4753_);
lean_dec(v_stop_4753_);
v_res_4757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4751_, v_i_boxed_4755_, v_stop_boxed_4756_, v_b_4754_);
lean_dec_ref(v_as_4751_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4763_, lean_object* v_args_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v___y_4773_; lean_object* v_lower_4774_; lean_object* v_upper_4775_; lean_object* v_j_4781_; lean_object* v___y_4783_; lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; 
v_j_4781_ = lean_unsigned_to_nat(0u);
v___x_4814_ = lean_array_get_size(v_args_4764_);
v___x_4815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4816_ = lean_nat_dec_lt(v_j_4781_, v___x_4814_);
if (v___x_4816_ == 0)
{
v___y_4783_ = v___x_4815_;
goto v___jp_4782_;
}
else
{
uint8_t v___x_4817_; 
v___x_4817_ = lean_nat_dec_le(v___x_4814_, v___x_4814_);
if (v___x_4817_ == 0)
{
if (v___x_4816_ == 0)
{
v___y_4783_ = v___x_4815_;
goto v___jp_4782_;
}
else
{
size_t v___x_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = lean_usize_of_nat(v___x_4814_);
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4764_, v___x_4818_, v___x_4819_, v___x_4815_);
v___y_4783_ = v___x_4820_;
goto v___jp_4782_;
}
}
else
{
size_t v___x_4821_; size_t v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = ((size_t)0ULL);
v___x_4822_ = lean_usize_of_nat(v___x_4814_);
v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4764_, v___x_4821_, v___x_4822_, v___x_4815_);
v___y_4783_ = v___x_4823_;
goto v___jp_4782_;
}
}
v___jp_4770_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4776_ = l_Array_toSubarray___redArg(v___y_4771_, v_lower_4774_, v_upper_4775_);
v___x_4777_ = l_Subarray_copy___redArg(v___x_4776_);
v___x_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
lean_ctor_set(v___x_4778_, 1, v___y_4772_);
v___x_4779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4779_, 0, v___y_4773_);
lean_ctor_set(v___x_4779_, 1, v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
v___jp_4782_:
{
uint8_t v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = 3;
v___x_4785_ = l_Lean_MVarId_generalize(v_goal_4763_, v___y_4783_, v___x_4784_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v_fst_4787_; lean_object* v_snd_4788_; lean_object* v___x_4789_; size_t v_sz_4790_; size_t v___x_4791_; lean_object* v___x_4792_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref_known(v___x_4785_, 1);
v_fst_4787_ = lean_ctor_get(v_a_4786_, 0);
lean_inc(v_fst_4787_);
v_snd_4788_ = lean_ctor_get(v_a_4786_, 1);
lean_inc(v_snd_4788_);
lean_dec(v_a_4786_);
v___x_4789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4790_ = lean_array_size(v_args_4764_);
v___x_4791_ = ((size_t)0ULL);
v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4787_, v_args_4764_, v_sz_4790_, v___x_4791_, v___x_4789_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v_fst_4794_; lean_object* v_snd_4795_; lean_object* v___x_4796_; uint8_t v___x_4797_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v___x_4792_, 1);
v_fst_4794_ = lean_ctor_get(v_a_4793_, 0);
lean_inc(v_fst_4794_);
v_snd_4795_ = lean_ctor_get(v_a_4793_, 1);
lean_inc(v_snd_4795_);
lean_dec(v_a_4793_);
v___x_4796_ = lean_array_get_size(v_fst_4787_);
v___x_4797_ = lean_nat_dec_le(v_snd_4795_, v_j_4781_);
if (v___x_4797_ == 0)
{
v___y_4771_ = v_fst_4787_;
v___y_4772_ = v_snd_4788_;
v___y_4773_ = v_fst_4794_;
v_lower_4774_ = v_snd_4795_;
v_upper_4775_ = v___x_4796_;
goto v___jp_4770_;
}
else
{
lean_dec(v_snd_4795_);
v___y_4771_ = v_fst_4787_;
v___y_4772_ = v_snd_4788_;
v___y_4773_ = v_fst_4794_;
v_lower_4774_ = v_j_4781_;
v_upper_4775_ = v___x_4796_;
goto v___jp_4770_;
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec(v_snd_4788_);
lean_dec(v_fst_4787_);
v_a_4798_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4792_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4792_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
v_a_4806_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4785_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4785_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4824_, lean_object* v_args_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4824_, v_args_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec_ref(v_args_4825_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4832_, lean_object* v_as_4833_, size_t v_sz_4834_, size_t v_i_4835_, lean_object* v_b_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4832_, v_as_4833_, v_sz_4834_, v_i_4835_, v_b_4836_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4843_, lean_object* v_as_4844_, lean_object* v_sz_4845_, lean_object* v_i_4846_, lean_object* v_b_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
size_t v_sz_boxed_4853_; size_t v_i_boxed_4854_; lean_object* v_res_4855_; 
v_sz_boxed_4853_ = lean_unbox_usize(v_sz_4845_);
lean_dec(v_sz_4845_);
v_i_boxed_4854_ = lean_unbox_usize(v_i_4846_);
lean_dec(v_i_4846_);
v_res_4855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4843_, v_as_4844_, v_sz_boxed_4853_, v_i_boxed_4854_, v_b_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec_ref(v_as_4844_);
lean_dec_ref(v_fst_4843_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4856_, size_t v_i_4857_, size_t v_stop_4858_, lean_object* v_b_4859_){
_start:
{
lean_object* v___y_4861_; uint8_t v___x_4865_; 
v___x_4865_ = lean_usize_dec_eq(v_i_4857_, v_stop_4858_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; lean_object* v_fst_4867_; 
v___x_4866_ = lean_array_uget_borrowed(v_as_4856_, v_i_4857_);
v_fst_4867_ = lean_ctor_get(v___x_4866_, 0);
if (lean_obj_tag(v_fst_4867_) == 0)
{
v___y_4861_ = v_b_4859_;
goto v___jp_4860_;
}
else
{
lean_object* v_val_4868_; lean_object* v___x_4869_; 
v_val_4868_ = lean_ctor_get(v_fst_4867_, 0);
lean_inc(v_val_4868_);
v___x_4869_ = lean_array_push(v_b_4859_, v_val_4868_);
v___y_4861_ = v___x_4869_;
goto v___jp_4860_;
}
}
else
{
return v_b_4859_;
}
v___jp_4860_:
{
size_t v___x_4862_; size_t v___x_4863_; 
v___x_4862_ = ((size_t)1ULL);
v___x_4863_ = lean_usize_add(v_i_4857_, v___x_4862_);
v_i_4857_ = v___x_4863_;
v_b_4859_ = v___y_4861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4870_, lean_object* v_i_4871_, lean_object* v_stop_4872_, lean_object* v_b_4873_){
_start:
{
size_t v_i_boxed_4874_; size_t v_stop_boxed_4875_; lean_object* v_res_4876_; 
v_i_boxed_4874_ = lean_unbox_usize(v_i_4871_);
lean_dec(v_i_4871_);
v_stop_boxed_4875_ = lean_unbox_usize(v_stop_4872_);
lean_dec(v_stop_4872_);
v_res_4876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4870_, v_i_boxed_4874_, v_stop_boxed_4875_, v_b_4873_);
lean_dec_ref(v_as_4870_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4879_, lean_object* v_start_4880_, lean_object* v_stop_4881_){
_start:
{
lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4882_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4883_ = lean_nat_dec_lt(v_start_4880_, v_stop_4881_);
if (v___x_4883_ == 0)
{
return v___x_4882_;
}
else
{
lean_object* v___x_4884_; uint8_t v___x_4885_; 
v___x_4884_ = lean_array_get_size(v_as_4879_);
v___x_4885_ = lean_nat_dec_le(v_stop_4881_, v___x_4884_);
if (v___x_4885_ == 0)
{
uint8_t v___x_4886_; 
v___x_4886_ = lean_nat_dec_lt(v_start_4880_, v___x_4884_);
if (v___x_4886_ == 0)
{
return v___x_4882_;
}
else
{
size_t v___x_4887_; size_t v___x_4888_; lean_object* v___x_4889_; 
v___x_4887_ = lean_usize_of_nat(v_start_4880_);
v___x_4888_ = lean_usize_of_nat(v___x_4884_);
v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4879_, v___x_4887_, v___x_4888_, v___x_4882_);
return v___x_4889_;
}
}
else
{
size_t v___x_4890_; size_t v___x_4891_; lean_object* v___x_4892_; 
v___x_4890_ = lean_usize_of_nat(v_start_4880_);
v___x_4891_ = lean_usize_of_nat(v_stop_4881_);
v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4879_, v___x_4890_, v___x_4891_, v___x_4882_);
return v___x_4892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4893_, lean_object* v_start_4894_, lean_object* v_stop_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4893_, v_start_4894_, v_stop_4895_);
lean_dec(v_stop_4895_);
lean_dec(v_start_4894_);
lean_dec_ref(v_as_4893_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4897_, lean_object* v_bs_4898_, lean_object* v_i_4899_, lean_object* v_cs_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4919_ = lean_array_get_size(v_as_4897_);
v___x_4920_ = lean_nat_dec_lt(v_i_4899_, v___x_4919_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; 
lean_dec(v_i_4899_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_cs_4900_);
return v___x_4921_;
}
else
{
lean_object* v___x_4922_; uint8_t v___x_4923_; 
v___x_4922_ = lean_array_get_size(v_bs_4898_);
v___x_4923_ = lean_nat_dec_lt(v_i_4899_, v___x_4922_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
lean_dec(v_i_4899_);
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v_cs_4900_);
return v___x_4924_;
}
else
{
lean_object* v_a_4925_; lean_object* v_fst_4926_; lean_object* v_snd_4927_; lean_object* v_fst_4929_; lean_object* v_snd_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v_b_4968_; 
v_a_4925_ = lean_array_fget_borrowed(v_as_4897_, v_i_4899_);
v_fst_4926_ = lean_ctor_get(v_a_4925_, 0);
lean_inc(v_fst_4926_);
v_snd_4927_ = lean_ctor_get(v_a_4925_, 1);
v_b_4968_ = lean_array_fget(v_bs_4898_, v_i_4899_);
if (lean_obj_tag(v_b_4968_) == 4)
{
lean_object* v_ref_4969_; lean_object* v_a_4970_; lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5006_; 
v_ref_4969_ = lean_ctor_get(v_b_4968_, 0);
v_a_4970_ = lean_ctor_get(v_b_4968_, 1);
v_a_4971_ = lean_ctor_get(v_b_4968_, 2);
v_isSharedCheck_5006_ = !lean_is_exclusive(v_b_4968_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4973_ = v_b_4968_;
v_isShared_4974_ = v_isSharedCheck_5006_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_inc(v_a_4970_);
lean_inc(v_ref_4969_);
lean_dec(v_b_4968_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5006_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v_toCold_4975_; lean_object* v_currRecDepth_4976_; lean_object* v_ref_4977_; uint8_t v_diag_4978_; uint8_t v_suppressElabErrors_4979_; lean_object* v_ref_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_toCold_4975_ = lean_ctor_get(v___y_4905_, 0);
v_currRecDepth_4976_ = lean_ctor_get(v___y_4905_, 1);
v_ref_4977_ = lean_ctor_get(v___y_4905_, 2);
v_diag_4978_ = lean_ctor_get_uint8(v___y_4905_, sizeof(void*)*3);
v_suppressElabErrors_4979_ = lean_ctor_get_uint8(v___y_4905_, sizeof(void*)*3 + 1);
v_ref_4980_ = l_Lean_replaceRef(v_ref_4969_, v_ref_4977_);
lean_inc(v_currRecDepth_4976_);
lean_inc_ref(v_toCold_4975_);
v___x_4981_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4981_, 0, v_toCold_4975_);
lean_ctor_set(v___x_4981_, 1, v_currRecDepth_4976_);
lean_ctor_set(v___x_4981_, 2, v_ref_4980_);
lean_ctor_set_uint8(v___x_4981_, sizeof(void*)*3, v_diag_4978_);
lean_ctor_set_uint8(v___x_4981_, sizeof(void*)*3 + 1, v_suppressElabErrors_4979_);
v___x_4982_ = l_Lean_Elab_Term_elabType(v_a_4971_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___x_4981_, v___y_4906_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc_n(v_a_4983_, 2);
lean_dec_ref_known(v___x_4982_, 1);
v___x_4984_ = l_Lean_Elab_Term_exprToSyntax(v_a_4983_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___x_4981_, v___y_4906_);
lean_dec_ref_known(v___x_4981_, 3);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4987_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 2, v_a_4985_);
v___x_4987_ = v___x_4973_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_ref_4969_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_a_4970_);
lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_a_4985_);
v___x_4987_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_a_4983_);
v_fst_4929_ = v___x_4987_;
v_snd_4930_ = v___x_4988_;
v___y_4931_ = v___y_4901_;
v___y_4932_ = v___y_4902_;
v___y_4933_ = v___y_4903_;
v___y_4934_ = v___y_4904_;
v___y_4935_ = v___y_4905_;
v___y_4936_ = v___y_4906_;
goto v___jp_4928_;
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec(v_a_4983_);
lean_del_object(v___x_4973_);
lean_dec_ref(v_a_4970_);
lean_dec(v_ref_4969_);
lean_dec(v_fst_4926_);
lean_dec_ref(v_cs_4900_);
lean_dec(v_i_4899_);
v_a_4990_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4984_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4984_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec_ref_known(v___x_4981_, 3);
lean_del_object(v___x_4973_);
lean_dec_ref(v_a_4970_);
lean_dec(v_ref_4969_);
lean_dec(v_fst_4926_);
lean_dec_ref(v_cs_4900_);
lean_dec(v_i_4899_);
v_a_4998_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4982_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4982_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
}
else
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_box(0);
v_fst_4929_ = v_b_4968_;
v_snd_4930_ = v___x_5007_;
v___y_4931_ = v___y_4901_;
v___y_4932_ = v___y_4902_;
v___y_4933_ = v___y_4903_;
v___y_4934_ = v___y_4904_;
v___y_4935_ = v___y_4905_;
v___y_4936_ = v___y_4906_;
goto v___jp_4928_;
}
v___jp_4928_:
{
lean_object* v___x_4937_; 
lean_inc(v_snd_4930_);
lean_inc(v_snd_4927_);
v___x_4937_ = l_Lean_Elab_Term_elabTerm(v_snd_4927_, v_snd_4930_, v___x_4923_, v___x_4923_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v_a_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___x_4937_, 1);
v___x_4939_ = lean_box(0);
v___x_4940_ = l_Lean_Elab_Term_ensureHasType(v_snd_4930_, v_a_4938_, v___x_4939_, v___x_4939_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v___x_4942_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v___x_4940_, 1);
v___x_4942_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4929_);
if (lean_obj_tag(v_fst_4926_) == 0)
{
v___y_4909_ = v_a_4941_;
v___y_4910_ = v___x_4942_;
v___y_4911_ = v_fst_4929_;
v___y_4912_ = v___x_4939_;
goto v___jp_4908_;
}
else
{
lean_object* v_val_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4951_; 
v_val_4943_ = lean_ctor_get(v_fst_4926_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_fst_4926_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4945_ = v_fst_4926_;
v_isShared_4946_ = v_isSharedCheck_4951_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_val_4943_);
lean_dec(v_fst_4926_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4951_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = l_Lean_TSyntax_getId(v_val_4943_);
lean_dec(v_val_4943_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v___x_4947_);
v___x_4949_ = v___x_4945_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
v___y_4909_ = v_a_4941_;
v___y_4910_ = v___x_4942_;
v___y_4911_ = v_fst_4929_;
v___y_4912_ = v___x_4949_;
goto v___jp_4908_;
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref(v_fst_4929_);
lean_dec(v_fst_4926_);
lean_dec_ref(v_cs_4900_);
lean_dec(v_i_4899_);
v_a_4952_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4940_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4940_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_snd_4930_);
lean_dec_ref(v_fst_4929_);
lean_dec(v_fst_4926_);
lean_dec_ref(v_cs_4900_);
lean_dec(v_i_4899_);
v_a_4960_ = lean_ctor_get(v___x_4937_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4937_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4937_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4937_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
}
}
v___jp_4908_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4913_, 0, v___y_4909_);
lean_ctor_set(v___x_4913_, 1, v___y_4910_);
lean_ctor_set(v___x_4913_, 2, v___y_4912_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___y_4911_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = lean_unsigned_to_nat(1u);
v___x_4916_ = lean_nat_add(v_i_4899_, v___x_4915_);
lean_dec(v_i_4899_);
v___x_4917_ = lean_array_push(v_cs_4900_, v___x_4914_);
v_i_4899_ = v___x_4916_;
v_cs_4900_ = v___x_4917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_5008_, lean_object* v_bs_5009_, lean_object* v_i_5010_, lean_object* v_cs_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_5008_, v_bs_5009_, v_i_5010_, v_cs_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec_ref(v_bs_5009_);
lean_dec_ref(v_as_5008_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5022_, lean_object* v_g_5023_, lean_object* v_pats_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5032_ = lean_array_mk(v_pats_5024_);
v___x_5033_ = lean_unsigned_to_nat(0u);
v___x_5034_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5035_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5022_, v___x_5032_, v___x_5033_, v___x_5034_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec_ref(v___x_5032_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5037_; lean_object* v_fst_5038_; lean_object* v_snd_5039_; lean_object* v___x_5040_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v___x_5037_ = l_Array_unzip___redArg(v_a_5036_);
lean_dec(v_a_5036_);
v_fst_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_fst_5038_);
v_snd_5039_ = lean_ctor_get(v___x_5037_, 1);
lean_inc(v_snd_5039_);
lean_dec_ref(v___x_5037_);
v___x_5040_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5023_, v_snd_5039_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v_snd_5039_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v_snd_5042_; lean_object* v_fst_5043_; lean_object* v_fst_5044_; lean_object* v_snd_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v_snd_5042_ = lean_ctor_get(v_a_5041_, 1);
lean_inc(v_snd_5042_);
v_fst_5043_ = lean_ctor_get(v_a_5041_, 0);
lean_inc(v_fst_5043_);
lean_dec(v_a_5041_);
v_fst_5044_ = lean_ctor_get(v_snd_5042_, 0);
lean_inc(v_fst_5044_);
v_snd_5045_ = lean_ctor_get(v_snd_5042_, 1);
lean_inc(v_snd_5045_);
lean_dec(v_snd_5042_);
v___x_5046_ = lean_array_get_size(v_tgts_5022_);
v___x_5047_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5022_, v___x_5033_, v___x_5046_);
v___x_5048_ = l_Array_zip___redArg(v___x_5047_, v_fst_5044_);
lean_dec(v_fst_5044_);
lean_dec_ref(v___x_5047_);
v___x_5049_ = lean_box(0);
v___x_5050_ = l_Array_zip___redArg(v_fst_5038_, v_fst_5043_);
lean_dec(v_fst_5043_);
lean_dec(v_fst_5038_);
v___x_5051_ = lean_array_to_list(v___x_5050_);
v___x_5052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5052_, 0, v___x_5048_);
v___x_5053_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5045_, v___x_5049_, v___x_5034_, v___x_5034_, v___x_5051_, v___x_5052_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5062_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5062_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5062_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
v___x_5058_ = lean_array_to_list(v_a_5054_);
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5058_);
v___x_5060_ = v___x_5056_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
v_a_5063_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_5053_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5053_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec(v_fst_5038_);
v_a_5071_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5040_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5040_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v_g_5023_);
v_a_5079_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5035_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5035_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5087_, lean_object* v_g_5088_, lean_object* v_pats_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5087_, v_g_5088_, v_pats_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec_ref(v_tgts_5087_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5098_, size_t v_sz_5099_, size_t v_i_5100_, lean_object* v_bs_5101_){
_start:
{
uint8_t v___x_5102_; 
v___x_5102_ = lean_usize_dec_lt(v_i_5100_, v_sz_5099_);
if (v___x_5102_ == 0)
{
return v_bs_5101_;
}
else
{
lean_object* v___x_5103_; uint8_t v___x_5104_; lean_object* v___x_5105_; lean_object* v_bs_x27_5106_; uint8_t v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; size_t v___x_5110_; size_t v___x_5111_; lean_object* v___x_5112_; 
v___x_5103_ = lean_unsigned_to_nat(1u);
v___x_5104_ = lean_nat_dec_eq(v___x_5098_, v___x_5103_);
v___x_5105_ = lean_unsigned_to_nat(0u);
v_bs_x27_5106_ = lean_array_uset(v_bs_5101_, v_i_5100_, v___x_5105_);
v___x_5107_ = 0;
v___x_5108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1));
v___x_5109_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1, v___x_5107_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 1, v___x_5104_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 2, v___x_5104_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 3, v___x_5104_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 4, v___x_5104_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 5, v___x_5104_);
lean_ctor_set_uint8(v___x_5109_, sizeof(void*)*1 + 6, v___x_5104_);
v___x_5110_ = ((size_t)1ULL);
v___x_5111_ = lean_usize_add(v_i_5100_, v___x_5110_);
v___x_5112_ = lean_array_uset(v_bs_x27_5106_, v_i_5100_, v___x_5109_);
v_i_5100_ = v___x_5111_;
v_bs_5101_ = v___x_5112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5114_, lean_object* v_sz_5115_, lean_object* v_i_5116_, lean_object* v_bs_5117_){
_start:
{
size_t v_sz_boxed_5118_; size_t v_i_boxed_5119_; lean_object* v_res_5120_; 
v_sz_boxed_5118_ = lean_unbox_usize(v_sz_5115_);
lean_dec(v_sz_5115_);
v_i_boxed_5119_ = lean_unbox_usize(v_i_5116_);
lean_dec(v_i_5116_);
v_res_5120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5114_, v_sz_boxed_5118_, v_i_boxed_5119_, v_bs_5117_);
lean_dec(v___x_5114_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5121_, lean_object* v___x_5122_, lean_object* v_pat_5123_, lean_object* v_tgts_5124_, lean_object* v___x_5125_, lean_object* v___f_5126_, lean_object* v_g_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
if (v___x_5121_ == 0)
{
lean_object* v___x_5135_; uint8_t v___x_5136_; lean_object* v___y_5138_; 
lean_dec(v_g_5127_);
v___x_5135_ = lean_unsigned_to_nat(1u);
v___x_5136_ = lean_nat_dec_eq(v___x_5122_, v___x_5135_);
if (v___x_5136_ == 0)
{
lean_object* v_ref_5147_; 
v_ref_5147_ = lean_ctor_get(v_pat_5123_, 0);
lean_inc(v_ref_5147_);
v___y_5138_ = v_ref_5147_;
goto v___jp_5137_;
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
lean_dec_ref(v_tgts_5124_);
v___x_5148_ = lean_box(0);
v___x_5149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5149_, 0, v_pat_5123_);
lean_ctor_set(v___x_5149_, 1, v___x_5148_);
lean_inc(v___y_5133_);
lean_inc_ref(v___y_5132_);
lean_inc(v___y_5131_);
lean_inc_ref(v___y_5130_);
lean_inc(v___y_5129_);
lean_inc_ref(v___y_5128_);
v___x_5150_ = lean_apply_8(v___f_5126_, v___x_5149_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, lean_box(0));
return v___x_5150_;
}
v___jp_5137_:
{
lean_object* v___x_5139_; lean_object* v_snd_5140_; size_t v_sz_5141_; size_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v_snd_5145_; lean_object* v___x_5146_; 
v___x_5139_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5123_);
v_snd_5140_ = lean_ctor_get(v___x_5139_, 1);
lean_inc(v_snd_5140_);
lean_dec_ref(v___x_5139_);
v_sz_5141_ = lean_array_size(v_tgts_5124_);
v___x_5142_ = ((size_t)0ULL);
v___x_5143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5122_, v_sz_5141_, v___x_5142_, v_tgts_5124_);
v___x_5144_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5138_, v___x_5143_, v___x_5136_, v___x_5125_, v_snd_5140_);
lean_dec_ref(v___x_5143_);
v_snd_5145_ = lean_ctor_get(v___x_5144_, 1);
lean_inc(v_snd_5145_);
lean_dec_ref(v___x_5144_);
lean_inc(v___y_5133_);
lean_inc_ref(v___y_5132_);
lean_inc(v___y_5131_);
lean_inc_ref(v___y_5130_);
lean_inc(v___y_5129_);
lean_inc_ref(v___y_5128_);
v___x_5146_ = lean_apply_8(v___f_5126_, v_snd_5145_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, lean_box(0));
return v___x_5146_;
}
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
lean_dec_ref(v___f_5126_);
lean_dec_ref(v_tgts_5124_);
lean_dec_ref(v_pat_5123_);
v___x_5151_ = lean_box(0);
v___x_5152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5152_, 0, v_g_5127_);
lean_ctor_set(v___x_5152_, 1, v___x_5151_);
v___x_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5154_, lean_object* v___x_5155_, lean_object* v_pat_5156_, lean_object* v_tgts_5157_, lean_object* v___x_5158_, lean_object* v___f_5159_, lean_object* v_g_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
uint8_t v___x_5045__boxed_5168_; lean_object* v_res_5169_; 
v___x_5045__boxed_5168_ = lean_unbox(v___x_5154_);
v_res_5169_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5045__boxed_5168_, v___x_5155_, v_pat_5156_, v_tgts_5157_, v___x_5158_, v___f_5159_, v_g_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___x_5158_);
lean_dec(v___x_5155_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5170_, lean_object* v_pat_5171_, lean_object* v_g_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v___f_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___y_5185_; uint8_t v___x_5186_; lean_object* v___x_5187_; 
lean_inc(v_g_5172_);
lean_inc_ref(v_tgts_5170_);
v___f_5180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5180_, 0, v_tgts_5170_);
lean_closure_set(v___f_5180_, 1, v_g_5172_);
v___x_5181_ = lean_array_get_size(v_tgts_5170_);
v___x_5182_ = lean_unsigned_to_nat(0u);
v___x_5183_ = lean_nat_dec_eq(v___x_5181_, v___x_5182_);
v___x_5184_ = lean_box(v___x_5183_);
v___y_5185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5185_, 0, v___x_5184_);
lean_closure_set(v___y_5185_, 1, v___x_5181_);
lean_closure_set(v___y_5185_, 2, v_pat_5171_);
lean_closure_set(v___y_5185_, 3, v_tgts_5170_);
lean_closure_set(v___y_5185_, 4, v___x_5182_);
lean_closure_set(v___y_5185_, 5, v___f_5180_);
lean_closure_set(v___y_5185_, 6, v_g_5172_);
v___x_5186_ = 1;
v___x_5187_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5185_, v___x_5186_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5188_, lean_object* v_pat_5189_, lean_object* v_g_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5188_, v_pat_5189_, v_g_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
lean_dec(v_a_5192_);
lean_dec_ref(v_a_5191_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5203_, lean_object* v_g_5204_, lean_object* v_pat_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_Lean_Elab_Term_elabType(v_ty_5203_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc_n(v_a_5214_, 2);
lean_dec_ref_known(v___x_5213_, 1);
v___x_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5215_, 0, v_a_5214_);
v___x_5216_ = 0;
v___x_5217_ = lean_box(0);
v___x_5218_ = l_Lean_Meta_mkFreshExprMVar(v___x_5215_, v___x_5216_, v___x_5217_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v___y_5221_; lean_object* v___x_5275_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
lean_inc(v_a_5219_);
lean_dec_ref_known(v___x_5218_, 1);
v___x_5275_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5205_);
if (lean_obj_tag(v___x_5275_) == 0)
{
v___y_5221_ = v___x_5217_;
goto v___jp_5220_;
}
else
{
lean_object* v_val_5276_; 
v_val_5276_ = lean_ctor_get(v___x_5275_, 0);
lean_inc(v_val_5276_);
lean_dec_ref_known(v___x_5275_, 1);
v___y_5221_ = v_val_5276_;
goto v___jp_5220_;
}
v___jp_5220_:
{
lean_object* v___x_5222_; 
lean_inc(v_a_5219_);
v___x_5222_ = l_Lean_MVarId_assert(v_g_5204_, v___y_5221_, v_a_5214_, v_a_5219_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v_a_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; 
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5223_);
lean_dec_ref_known(v___x_5222_, 1);
v___x_5224_ = 0;
v___x_5225_ = l_Lean_Meta_intro1Core(v_a_5223_, v___x_5224_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v_fst_5227_; lean_object* v_snd_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5258_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v_fst_5227_ = lean_ctor_get(v_a_5226_, 0);
v_snd_5228_ = lean_ctor_get(v_a_5226_, 1);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_a_5226_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5230_ = v_a_5226_;
v_isShared_5231_ = v_isSharedCheck_5258_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_snd_5228_);
lean_inc(v_fst_5227_);
lean_dec(v_a_5226_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5258_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5232_ = lean_box(0);
v___x_5233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5234_ = l_Lean_Expr_fvar___override(v_fst_5227_);
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5236_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5228_, v___x_5232_, v___x_5233_, v___x_5234_, v___x_5233_, v_pat_5205_, v___x_5235_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
lean_dec_ref(v___x_5234_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5249_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5239_ = v___x_5236_;
v_isShared_5240_ = v_isSharedCheck_5249_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5236_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5249_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5244_; 
v___x_5241_ = l_Lean_Expr_mvarId_x21(v_a_5219_);
lean_dec(v_a_5219_);
v___x_5242_ = lean_array_to_list(v_a_5237_);
if (v_isShared_5231_ == 0)
{
lean_ctor_set_tag(v___x_5230_, 1);
lean_ctor_set(v___x_5230_, 1, v___x_5242_);
lean_ctor_set(v___x_5230_, 0, v___x_5241_);
v___x_5244_ = v___x_5230_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v___x_5242_);
v___x_5244_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
lean_object* v___x_5246_; 
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 0, v___x_5244_);
v___x_5246_ = v___x_5239_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5244_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_del_object(v___x_5230_);
lean_dec(v_a_5219_);
v_a_5250_ = lean_ctor_get(v___x_5236_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5236_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5236_);
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
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec(v_a_5219_);
lean_dec_ref(v_pat_5205_);
v_a_5259_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5225_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5225_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec(v_a_5219_);
lean_dec_ref(v_pat_5205_);
v_a_5267_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5222_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5222_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
lean_dec(v_a_5214_);
lean_dec_ref(v_pat_5205_);
lean_dec(v_g_5204_);
v_a_5277_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5218_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5218_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
lean_dec_ref(v_pat_5205_);
lean_dec(v_g_5204_);
v_a_5285_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5213_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5213_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5293_, lean_object* v_g_5294_, lean_object* v_pat_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5293_, v_g_5294_, v_pat_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5304_, lean_object* v_ty_5305_, lean_object* v_g_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v___f_5314_; uint8_t v___x_5315_; lean_object* v___x_5316_; 
v___f_5314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5314_, 0, v_ty_5305_);
lean_closure_set(v___f_5314_, 1, v_g_5306_);
lean_closure_set(v___f_5314_, 2, v_pat_5304_);
v___x_5315_ = 1;
v___x_5316_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5314_, v___x_5315_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5317_, lean_object* v_ty_5318_, lean_object* v_g_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5317_, v_ty_5318_, v_g_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5335_, lean_object* v_acc_5336_, lean_object* v_ty_x3f_5337_){
_start:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = lean_array_get_size(v_pats_5335_);
v___x_5340_ = lean_nat_dec_lt(v___x_5338_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_dec(v_ty_x3f_5337_);
return v_acc_5336_;
}
else
{
uint8_t v___x_5341_; 
v___x_5341_ = lean_nat_dec_le(v___x_5339_, v___x_5339_);
if (v___x_5341_ == 0)
{
if (v___x_5340_ == 0)
{
lean_dec(v_ty_x3f_5337_);
return v_acc_5336_;
}
else
{
size_t v___x_5342_; size_t v___x_5343_; lean_object* v___x_5344_; 
v___x_5342_ = ((size_t)0ULL);
v___x_5343_ = lean_usize_of_nat(v___x_5339_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5337_, v_pats_5335_, v___x_5342_, v___x_5343_, v_acc_5336_);
return v___x_5344_;
}
}
else
{
size_t v___x_5345_; size_t v___x_5346_; lean_object* v___x_5347_; 
v___x_5345_ = ((size_t)0ULL);
v___x_5346_ = lean_usize_of_nat(v___x_5339_);
v___x_5347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5337_, v_pats_5335_, v___x_5345_, v___x_5346_, v_acc_5336_);
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5351_, lean_object* v_acc_5352_, lean_object* v_ty_x3f_5353_){
_start:
{
lean_object* v___x_5354_; uint8_t v___x_5355_; 
v___x_5354_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5351_);
v___x_5355_ = l_Lean_Syntax_isOfKind(v_pat_5351_, v___x_5354_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; uint8_t v___x_5357_; 
v___x_5356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5351_);
v___x_5357_ = l_Lean_Syntax_isOfKind(v_pat_5351_, v___x_5356_);
if (v___x_5357_ == 0)
{
lean_dec(v_ty_x3f_5353_);
lean_dec(v_pat_5351_);
return v_acc_5352_;
}
else
{
lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; uint8_t v___x_5362_; 
v___x_5358_ = lean_unsigned_to_nat(1u);
v___x_5359_ = l_Lean_Syntax_getArg(v_pat_5351_, v___x_5358_);
v___x_5360_ = lean_unsigned_to_nat(2u);
v___x_5361_ = l_Lean_Syntax_getArg(v_pat_5351_, v___x_5360_);
lean_dec(v_pat_5351_);
v___x_5362_ = l_Lean_Syntax_isNone(v___x_5361_);
if (v___x_5362_ == 0)
{
uint8_t v___x_5363_; 
lean_dec(v_ty_x3f_5353_);
lean_inc(v___x_5361_);
v___x_5363_ = l_Lean_Syntax_matchesNull(v___x_5361_, v___x_5360_);
if (v___x_5363_ == 0)
{
lean_dec(v___x_5361_);
lean_dec(v___x_5359_);
return v_acc_5352_;
}
else
{
lean_object* v_ty_x3f_x27_5364_; lean_object* v___x_5365_; lean_object* v_pats_5366_; lean_object* v___x_5367_; 
v_ty_x3f_x27_5364_ = l_Lean_Syntax_getArg(v___x_5361_, v___x_5358_);
lean_dec(v___x_5361_);
v___x_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_ty_x3f_x27_5364_);
v_pats_5366_ = l_Lean_Syntax_getArgs(v___x_5359_);
lean_dec(v___x_5359_);
v___x_5367_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5366_, v_acc_5352_, v___x_5365_);
lean_dec_ref(v_pats_5366_);
return v___x_5367_;
}
}
else
{
lean_object* v_pats_5368_; lean_object* v___x_5369_; 
lean_dec(v___x_5361_);
v_pats_5368_ = l_Lean_Syntax_getArgs(v___x_5359_);
lean_dec(v___x_5359_);
v___x_5369_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5368_, v_acc_5352_, v_ty_x3f_5353_);
lean_dec_ref(v_pats_5368_);
return v___x_5369_;
}
}
}
else
{
lean_object* v___x_5370_; lean_object* v_p_5371_; 
v___x_5370_ = lean_unsigned_to_nat(0u);
v_p_5371_ = l_Lean_Syntax_getArg(v_pat_5351_, v___x_5370_);
lean_dec(v_pat_5351_);
if (lean_obj_tag(v_ty_x3f_5353_) == 0)
{
lean_object* v___x_5372_; 
v___x_5372_ = lean_array_push(v_acc_5352_, v_p_5371_);
return v___x_5372_;
}
else
{
lean_object* v_val_5373_; lean_object* v___x_5374_; lean_object* v_ref_5375_; uint8_t v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v_val_5373_ = lean_ctor_get(v_ty_x3f_5353_, 0);
lean_inc(v_val_5373_);
lean_dec_ref_known(v_ty_x3f_5353_, 1);
v___x_5374_ = lean_box(0);
v_ref_5375_ = l_Lean_replaceRef(v_p_5371_, v___x_5374_);
v___x_5376_ = 0;
v___x_5377_ = l_Lean_SourceInfo_fromRef(v_ref_5375_, v___x_5376_);
lean_dec(v_ref_5375_);
v___x_5378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5377_, 7);
v___x_5380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5377_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
v___x_5381_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5382_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5383_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5384_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5383_, v_p_5371_);
v___x_5385_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5382_, v___x_5384_);
v___x_5386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5377_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node2(v___x_5377_, v___x_5383_, v___x_5387_, v_val_5373_);
v___x_5389_ = l_Lean_Syntax_node2(v___x_5377_, v___x_5381_, v___x_5385_, v___x_5388_);
v___x_5390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5377_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
v___x_5392_ = l_Lean_Syntax_node3(v___x_5377_, v___x_5378_, v___x_5380_, v___x_5389_, v___x_5391_);
v___x_5393_ = lean_array_push(v_acc_5352_, v___x_5392_);
return v___x_5393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5394_, lean_object* v_as_5395_, size_t v_i_5396_, size_t v_stop_5397_, lean_object* v_b_5398_){
_start:
{
uint8_t v___x_5399_; 
v___x_5399_ = lean_usize_dec_eq(v_i_5396_, v_stop_5397_);
if (v___x_5399_ == 0)
{
lean_object* v___x_5400_; lean_object* v___x_5401_; size_t v___x_5402_; size_t v___x_5403_; 
v___x_5400_ = lean_array_uget_borrowed(v_as_5395_, v_i_5396_);
lean_inc(v_ty_x3f_5394_);
lean_inc(v___x_5400_);
v___x_5401_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5400_, v_b_5398_, v_ty_x3f_5394_);
v___x_5402_ = ((size_t)1ULL);
v___x_5403_ = lean_usize_add(v_i_5396_, v___x_5402_);
v_i_5396_ = v___x_5403_;
v_b_5398_ = v___x_5401_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5394_);
return v_b_5398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5405_, lean_object* v_as_5406_, lean_object* v_i_5407_, lean_object* v_stop_5408_, lean_object* v_b_5409_){
_start:
{
size_t v_i_boxed_5410_; size_t v_stop_boxed_5411_; lean_object* v_res_5412_; 
v_i_boxed_5410_ = lean_unbox_usize(v_i_5407_);
lean_dec(v_i_5407_);
v_stop_boxed_5411_ = lean_unbox_usize(v_stop_5408_);
lean_dec(v_stop_5408_);
v_res_5412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5405_, v_as_5406_, v_i_boxed_5410_, v_stop_boxed_5411_, v_b_5409_);
lean_dec_ref(v_as_5406_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5413_, lean_object* v_acc_5414_, lean_object* v_ty_x3f_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5413_, v_acc_5414_, v_ty_x3f_5415_);
lean_dec_ref(v_pats_5413_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5422_, lean_object* v_pats_5423_, lean_object* v_ty_x3f_5424_, lean_object* v_cont_5425_, lean_object* v_i_5426_, lean_object* v_g_5427_, lean_object* v_fs_5428_, lean_object* v_clears_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5422_, v_pats_5423_, v_ty_x3f_5424_, v_cont_5425_, v_i_5426_, v_g_5427_, v_fs_5428_, v_clears_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
lean_dec(v_i_5426_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5439_ = _args[0];
lean_object* v_ref_5440_ = _args[1];
lean_object* v_pats_5441_ = _args[2];
lean_object* v_ty_x3f_5442_ = _args[3];
lean_object* v_cont_5443_ = _args[4];
lean_object* v_i_5444_ = _args[5];
lean_object* v_g_5445_ = _args[6];
lean_object* v_fs_5446_ = _args[7];
lean_object* v_clears_5447_ = _args[8];
lean_object* v_a_5448_ = _args[9];
lean_object* v_a_5449_ = _args[10];
lean_object* v_a_5450_ = _args[11];
lean_object* v_a_5451_ = _args[12];
lean_object* v_a_5452_ = _args[13];
lean_object* v_a_5453_ = _args[14];
lean_object* v_a_5454_ = _args[15];
lean_object* v_a_5455_ = _args[16];
_start:
{
lean_object* v_res_5456_; 
v_res_5456_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5439_, v_ref_5440_, v_pats_5441_, v_ty_x3f_5442_, v_cont_5443_, v_i_5444_, v_g_5445_, v_fs_5446_, v_clears_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
lean_dec(v_a_5454_);
lean_dec_ref(v_a_5453_);
lean_dec(v_a_5452_);
lean_dec_ref(v_a_5451_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_i_5444_);
return v_res_5456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5457_, lean_object* v_fs_5458_, lean_object* v_clears_5459_, lean_object* v_ref_5460_, lean_object* v_pats_5461_, lean_object* v_ty_x3f_5462_, lean_object* v_a_5463_, lean_object* v_cont_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5472_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5457_);
v___x_5473_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5473_, 0, lean_box(0));
lean_closure_set(v___x_5473_, 1, v_ref_5460_);
lean_closure_set(v___x_5473_, 2, v_pats_5461_);
lean_closure_set(v___x_5473_, 3, v_ty_x3f_5462_);
lean_closure_set(v___x_5473_, 4, v_cont_5464_);
lean_closure_set(v___x_5473_, 5, v___x_5472_);
lean_closure_set(v___x_5473_, 6, v_g_5457_);
lean_closure_set(v___x_5473_, 7, v_fs_5458_);
lean_closure_set(v___x_5473_, 8, v_clears_5459_);
lean_closure_set(v___x_5473_, 9, v_a_5463_);
v___x_5474_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5457_, v___x_5473_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5475_, lean_object* v_fs_5476_, lean_object* v_clears_5477_, lean_object* v_a_5478_, lean_object* v_ref_5479_, lean_object* v_pat_5480_, lean_object* v_ty_x3f_5481_, lean_object* v_cont_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___x_5502_; uint8_t v___x_5503_; 
v___x_5502_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5480_);
v___x_5503_ = l_Lean_Syntax_isOfKind(v_pat_5480_, v___x_5502_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; uint8_t v___x_5505_; 
lean_dec(v_ref_5479_);
v___x_5504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5480_);
v___x_5505_ = l_Lean_Syntax_isOfKind(v_pat_5480_, v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; 
lean_dec_ref(v_cont_5482_);
lean_dec(v_ty_x3f_5481_);
lean_dec(v_pat_5480_);
lean_dec(v_a_5478_);
lean_dec_ref(v_clears_5477_);
lean_dec(v_fs_5476_);
lean_dec(v_g_5475_);
v___x_5506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5506_;
}
else
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v_ty_x3f_x27_5510_; lean_object* v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; 
v___x_5507_ = lean_unsigned_to_nat(1u);
v___x_5508_ = l_Lean_Syntax_getArg(v_pat_5480_, v___x_5507_);
v___x_5521_ = lean_unsigned_to_nat(2u);
v___x_5522_ = l_Lean_Syntax_getArg(v_pat_5480_, v___x_5521_);
v___x_5523_ = l_Lean_Syntax_isNone(v___x_5522_);
if (v___x_5523_ == 0)
{
uint8_t v___x_5524_; 
lean_inc(v___x_5522_);
v___x_5524_ = l_Lean_Syntax_matchesNull(v___x_5522_, v___x_5521_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5525_; 
lean_dec(v___x_5522_);
lean_dec(v___x_5508_);
lean_dec_ref(v_cont_5482_);
lean_dec(v_ty_x3f_5481_);
lean_dec(v_pat_5480_);
lean_dec(v_a_5478_);
lean_dec_ref(v_clears_5477_);
lean_dec(v_fs_5476_);
lean_dec(v_g_5475_);
v___x_5525_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5525_;
}
else
{
lean_object* v_ty_x3f_x27_5526_; lean_object* v___x_5527_; 
v_ty_x3f_x27_5526_ = l_Lean_Syntax_getArg(v___x_5522_, v___x_5507_);
lean_dec(v___x_5522_);
v___x_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5527_, 0, v_ty_x3f_x27_5526_);
v_ty_x3f_x27_5510_ = v___x_5527_;
v___y_5511_ = v_a_5483_;
v___y_5512_ = v_a_5484_;
v___y_5513_ = v_a_5485_;
v___y_5514_ = v_a_5486_;
v___y_5515_ = v_a_5487_;
v___y_5516_ = v_a_5488_;
goto v___jp_5509_;
}
}
else
{
lean_object* v___x_5528_; 
lean_dec(v___x_5522_);
v___x_5528_ = lean_box(0);
v_ty_x3f_x27_5510_ = v___x_5528_;
v___y_5511_ = v_a_5483_;
v___y_5512_ = v_a_5484_;
v___y_5513_ = v_a_5485_;
v___y_5514_ = v_a_5486_;
v___y_5515_ = v_a_5487_;
v___y_5516_ = v_a_5488_;
goto v___jp_5509_;
}
v___jp_5509_:
{
lean_object* v_pats_5517_; lean_object* v___x_5518_; uint8_t v___x_5519_; 
v_pats_5517_ = l_Lean_Syntax_getArgs(v___x_5508_);
lean_dec(v___x_5508_);
v___x_5518_ = lean_array_get_size(v_pats_5517_);
v___x_5519_ = lean_nat_dec_eq(v___x_5518_, v___x_5507_);
if (v___x_5519_ == 0)
{
lean_object* v___x_5520_; 
lean_dec(v_pat_5480_);
v___x_5520_ = lean_box(0);
v___y_5491_ = v___y_5514_;
v___y_5492_ = v___y_5515_;
v___y_5493_ = v___y_5516_;
v___y_5494_ = v___y_5512_;
v___y_5495_ = v___y_5513_;
v___y_5496_ = v_ty_x3f_x27_5510_;
v___y_5497_ = v_pats_5517_;
v___y_5498_ = v___y_5511_;
v___y_5499_ = v___x_5520_;
goto v___jp_5490_;
}
else
{
v___y_5491_ = v___y_5514_;
v___y_5492_ = v___y_5515_;
v___y_5493_ = v___y_5516_;
v___y_5494_ = v___y_5512_;
v___y_5495_ = v___y_5513_;
v___y_5496_ = v_ty_x3f_x27_5510_;
v___y_5497_ = v_pats_5517_;
v___y_5498_ = v___y_5511_;
v___y_5499_ = v_pat_5480_;
goto v___jp_5490_;
}
}
}
}
else
{
lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5529_ = lean_unsigned_to_nat(0u);
v___x_5530_ = l_Lean_Syntax_getArg(v_pat_5480_, v___x_5529_);
lean_dec(v_pat_5480_);
v___x_5531_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5530_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; lean_object* v___x_5533_; lean_object* v___y_5535_; lean_object* v___y_5536_; lean_object* v___y_5559_; lean_object* v_ref_5563_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
lean_inc(v_a_5532_);
lean_dec_ref_known(v___x_5531_, 1);
v___x_5533_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5479_, v_a_5532_, v_ty_x3f_5481_);
lean_dec(v_ty_x3f_5481_);
v_ref_5563_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_ref_5563_);
v___y_5559_ = v_ref_5563_;
goto v___jp_5558_;
v___jp_5534_:
{
lean_object* v_toCold_5537_; lean_object* v_currRecDepth_5538_; lean_object* v_ref_5539_; uint8_t v_diag_5540_; uint8_t v_suppressElabErrors_5541_; lean_object* v_ref_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; 
v_toCold_5537_ = lean_ctor_get(v_a_5487_, 0);
v_currRecDepth_5538_ = lean_ctor_get(v_a_5487_, 1);
v_ref_5539_ = lean_ctor_get(v_a_5487_, 2);
v_diag_5540_ = lean_ctor_get_uint8(v_a_5487_, sizeof(void*)*3);
v_suppressElabErrors_5541_ = lean_ctor_get_uint8(v_a_5487_, sizeof(void*)*3 + 1);
v_ref_5542_ = l_Lean_replaceRef(v___y_5535_, v_ref_5539_);
lean_dec(v___y_5535_);
lean_inc(v_currRecDepth_5538_);
lean_inc_ref(v_toCold_5537_);
v___x_5543_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5543_, 0, v_toCold_5537_);
lean_ctor_set(v___x_5543_, 1, v_currRecDepth_5538_);
lean_ctor_set(v___x_5543_, 2, v_ref_5542_);
lean_ctor_set_uint8(v___x_5543_, sizeof(void*)*3, v_diag_5540_);
lean_ctor_set_uint8(v___x_5543_, sizeof(void*)*3 + 1, v_suppressElabErrors_5541_);
v___x_5544_ = l_Lean_MVarId_intro(v_g_5475_, v___y_5536_, v_a_5485_, v_a_5486_, v___x_5543_, v_a_5488_);
lean_dec_ref_known(v___x_5543_, 3);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v_a_5545_; lean_object* v_fst_5546_; lean_object* v_snd_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v_a_5545_ = lean_ctor_get(v___x_5544_, 0);
lean_inc(v_a_5545_);
lean_dec_ref_known(v___x_5544_, 1);
v_fst_5546_ = lean_ctor_get(v_a_5545_, 0);
lean_inc(v_fst_5546_);
v_snd_5547_ = lean_ctor_get(v_a_5545_, 1);
lean_inc(v_snd_5547_);
lean_dec(v_a_5545_);
v___x_5548_ = l_Lean_Expr_fvar___override(v_fst_5546_);
v___x_5549_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5547_, v_fs_5476_, v_clears_5477_, v___x_5548_, v_a_5478_, v___x_5533_, v_cont_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_);
lean_dec_ref(v___x_5548_);
return v___x_5549_;
}
else
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5557_; 
lean_dec_ref(v___x_5533_);
lean_dec_ref(v_cont_5482_);
lean_dec(v_a_5478_);
lean_dec_ref(v_clears_5477_);
lean_dec(v_fs_5476_);
v_a_5550_ = lean_ctor_get(v___x_5544_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5552_ = v___x_5544_;
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5544_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5555_; 
if (v_isShared_5553_ == 0)
{
v___x_5555_ = v___x_5552_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_a_5550_);
v___x_5555_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
return v___x_5555_;
}
}
}
}
v___jp_5558_:
{
lean_object* v___x_5560_; 
v___x_5560_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5533_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v___x_5561_; 
v___x_5561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5535_ = v___y_5559_;
v___y_5536_ = v___x_5561_;
goto v___jp_5534_;
}
else
{
lean_object* v_val_5562_; 
v_val_5562_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_val_5562_);
lean_dec_ref_known(v___x_5560_, 1);
v___y_5535_ = v___y_5559_;
v___y_5536_ = v_val_5562_;
goto v___jp_5534_;
}
}
}
else
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5571_; 
lean_dec_ref(v_cont_5482_);
lean_dec(v_ty_x3f_5481_);
lean_dec(v_ref_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_clears_5477_);
lean_dec(v_fs_5476_);
lean_dec(v_g_5475_);
v_a_5564_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5571_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5571_ == 0)
{
v___x_5566_ = v___x_5531_;
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5531_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5571_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5569_; 
if (v_isShared_5567_ == 0)
{
v___x_5569_ = v___x_5566_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
return v___x_5569_;
}
}
}
}
v___jp_5490_:
{
if (lean_obj_tag(v___y_5496_) == 0)
{
lean_object* v___x_5500_; 
v___x_5500_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5475_, v_fs_5476_, v_clears_5477_, v___y_5499_, v___y_5497_, v_ty_x3f_5481_, v_a_5478_, v_cont_5482_, v___y_5498_, v___y_5494_, v___y_5495_, v___y_5491_, v___y_5492_, v___y_5493_);
return v___x_5500_;
}
else
{
lean_object* v___x_5501_; 
lean_dec(v_ty_x3f_5481_);
v___x_5501_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5475_, v_fs_5476_, v_clears_5477_, v___y_5499_, v___y_5497_, v___y_5496_, v_a_5478_, v_cont_5482_, v___y_5498_, v___y_5494_, v___y_5495_, v___y_5491_, v___y_5492_, v___y_5493_);
return v___x_5501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5572_, lean_object* v_pats_5573_, lean_object* v_ty_x3f_5574_, lean_object* v_cont_5575_, lean_object* v_i_5576_, lean_object* v_g_5577_, lean_object* v_fs_5578_, lean_object* v_clears_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_){
_start:
{
lean_object* v___x_5588_; uint8_t v___x_5589_; 
v___x_5588_ = lean_array_get_size(v_pats_5573_);
v___x_5589_ = lean_nat_dec_lt(v_i_5576_, v___x_5588_);
if (v___x_5589_ == 0)
{
lean_object* v___x_5590_; 
lean_dec(v_ty_x3f_5574_);
lean_dec_ref(v_pats_5573_);
lean_dec(v_ref_5572_);
lean_inc(v_a_5586_);
lean_inc_ref(v_a_5585_);
lean_inc(v_a_5584_);
lean_inc_ref(v_a_5583_);
lean_inc(v_a_5582_);
lean_inc_ref(v_a_5581_);
v___x_5590_ = lean_apply_11(v_cont_5575_, v_g_5577_, v_fs_5578_, v_clears_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, lean_box(0));
return v___x_5590_;
}
else
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; 
v___x_5591_ = lean_array_fget(v_pats_5573_, v_i_5576_);
v___x_5592_ = lean_unsigned_to_nat(1u);
v___x_5593_ = lean_nat_add(v_i_5576_, v___x_5592_);
lean_inc(v_ty_x3f_5574_);
lean_inc(v_ref_5572_);
v___x_5594_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5594_, 0, v_ref_5572_);
lean_closure_set(v___x_5594_, 1, v_pats_5573_);
lean_closure_set(v___x_5594_, 2, v_ty_x3f_5574_);
lean_closure_set(v___x_5594_, 3, v_cont_5575_);
lean_closure_set(v___x_5594_, 4, v___x_5593_);
v___x_5595_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5577_, v_fs_5578_, v_clears_5579_, v_a_5580_, v_ref_5572_, v___x_5591_, v_ty_x3f_5574_, v___x_5594_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_);
return v___x_5595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5596_, lean_object* v_ref_5597_, lean_object* v_pats_5598_, lean_object* v_ty_x3f_5599_, lean_object* v_cont_5600_, lean_object* v_i_5601_, lean_object* v_g_5602_, lean_object* v_fs_5603_, lean_object* v_clears_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_){
_start:
{
lean_object* v___x_5613_; 
v___x_5613_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5597_, v_pats_5598_, v_ty_x3f_5599_, v_cont_5600_, v_i_5601_, v_g_5602_, v_fs_5603_, v_clears_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5614_, lean_object* v_fs_5615_, lean_object* v_clears_5616_, lean_object* v_ref_5617_, lean_object* v_pats_5618_, lean_object* v_ty_x3f_5619_, lean_object* v_a_5620_, lean_object* v_cont_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5614_, v_fs_5615_, v_clears_5616_, v_ref_5617_, v_pats_5618_, v_ty_x3f_5619_, v_a_5620_, v_cont_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_);
lean_dec(v_a_5627_);
lean_dec_ref(v_a_5626_);
lean_dec(v_a_5625_);
lean_dec_ref(v_a_5624_);
lean_dec(v_a_5623_);
lean_dec_ref(v_a_5622_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5630_, lean_object* v_fs_5631_, lean_object* v_clears_5632_, lean_object* v_a_5633_, lean_object* v_ref_5634_, lean_object* v_pat_5635_, lean_object* v_ty_x3f_5636_, lean_object* v_cont_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_){
_start:
{
lean_object* v_res_5645_; 
v_res_5645_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5630_, v_fs_5631_, v_clears_5632_, v_a_5633_, v_ref_5634_, v_pat_5635_, v_ty_x3f_5636_, v_cont_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_);
lean_dec(v_a_5643_);
lean_dec_ref(v_a_5642_);
lean_dec(v_a_5641_);
lean_dec_ref(v_a_5640_);
lean_dec(v_a_5639_);
lean_dec_ref(v_a_5638_);
return v_res_5645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
lean_object* v___x_5654_; 
v___x_5654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_){
_start:
{
lean_object* v_res_5663_; 
v_res_5663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
lean_dec(v___y_5661_);
lean_dec_ref(v___y_5660_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5664_, lean_object* v_g_5665_, lean_object* v_fs_5666_, lean_object* v_clears_5667_, lean_object* v_a_5668_, lean_object* v_ref_5669_, lean_object* v_pat_5670_, lean_object* v_ty_x3f_5671_, lean_object* v_cont_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v___x_5680_; 
v___x_5680_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5665_, v_fs_5666_, v_clears_5667_, v_a_5668_, v_ref_5669_, v_pat_5670_, v_ty_x3f_5671_, v_cont_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5681_, lean_object* v_g_5682_, lean_object* v_fs_5683_, lean_object* v_clears_5684_, lean_object* v_a_5685_, lean_object* v_ref_5686_, lean_object* v_pat_5687_, lean_object* v_ty_x3f_5688_, lean_object* v_cont_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5681_, v_g_5682_, v_fs_5683_, v_clears_5684_, v_a_5685_, v_ref_5686_, v_pat_5687_, v_ty_x3f_5688_, v_cont_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
lean_dec(v_a_5691_);
lean_dec_ref(v_a_5690_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5698_, lean_object* v_g_5699_, lean_object* v_fs_5700_, lean_object* v_clears_5701_, lean_object* v_ref_5702_, lean_object* v_pats_5703_, lean_object* v_ty_x3f_5704_, lean_object* v_a_5705_, lean_object* v_cont_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v___x_5714_; 
v___x_5714_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5699_, v_fs_5700_, v_clears_5701_, v_ref_5702_, v_pats_5703_, v_ty_x3f_5704_, v_a_5705_, v_cont_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_);
return v___x_5714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5715_, lean_object* v_g_5716_, lean_object* v_fs_5717_, lean_object* v_clears_5718_, lean_object* v_ref_5719_, lean_object* v_pats_5720_, lean_object* v_ty_x3f_5721_, lean_object* v_a_5722_, lean_object* v_cont_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5715_, v_g_5716_, v_fs_5717_, v_clears_5718_, v_ref_5719_, v_pats_5720_, v_ty_x3f_5721_, v_a_5722_, v_cont_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_);
lean_dec(v_a_5729_);
lean_dec_ref(v_a_5728_);
lean_dec(v_a_5727_);
lean_dec_ref(v_a_5726_);
lean_dec(v_a_5725_);
lean_dec_ref(v_a_5724_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5732_, lean_object* v___x_5733_, lean_object* v___x_5734_, lean_object* v___x_5735_, lean_object* v_pats_5736_, lean_object* v_ty_x3f_5737_, lean_object* v___x_5738_, lean_object* v___x_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5732_, v___x_5733_, v___x_5734_, v___x_5735_, v_pats_5736_, v_ty_x3f_5737_, v___x_5738_, v___x_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5756_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5750_ = v___x_5747_;
v_isShared_5751_ = v_isSharedCheck_5756_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5747_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5756_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5752_; lean_object* v___x_5754_; 
v___x_5752_ = lean_array_to_list(v_a_5748_);
if (v_isShared_5751_ == 0)
{
lean_ctor_set(v___x_5750_, 0, v___x_5752_);
v___x_5754_ = v___x_5750_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5752_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
v_a_5757_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5747_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5747_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5765_, lean_object* v___x_5766_, lean_object* v___x_5767_, lean_object* v___x_5768_, lean_object* v_pats_5769_, lean_object* v_ty_x3f_5770_, lean_object* v___x_5771_, lean_object* v___x_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_){
_start:
{
lean_object* v_res_5780_; 
v_res_5780_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5765_, v___x_5766_, v___x_5767_, v___x_5768_, v_pats_5769_, v_ty_x3f_5770_, v___x_5771_, v___x_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_);
lean_dec(v___y_5778_);
lean_dec_ref(v___y_5777_);
lean_dec(v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
return v_res_5780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5781_, lean_object* v_ty_x3f_5782_, lean_object* v_g_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_){
_start:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___f_5795_; uint8_t v___x_5796_; lean_object* v___x_5797_; 
v___x_5791_ = lean_box(0);
v___x_5792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5793_ = lean_box(0);
v___x_5794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5795_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5795_, 0, v_g_5783_);
lean_closure_set(v___f_5795_, 1, v___x_5791_);
lean_closure_set(v___f_5795_, 2, v___x_5792_);
lean_closure_set(v___f_5795_, 3, v___x_5793_);
lean_closure_set(v___f_5795_, 4, v_pats_5781_);
lean_closure_set(v___f_5795_, 5, v_ty_x3f_5782_);
lean_closure_set(v___f_5795_, 6, v___x_5792_);
lean_closure_set(v___f_5795_, 7, v___x_5794_);
v___x_5796_ = 1;
v___x_5797_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5795_, v___x_5796_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_);
return v___x_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5798_, lean_object* v_ty_x3f_5799_, lean_object* v_g_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_){
_start:
{
lean_object* v_res_5808_; 
v_res_5808_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5798_, v_ty_x3f_5799_, v_g_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_, v_a_5806_);
lean_dec(v_a_5806_);
lean_dec_ref(v_a_5805_);
lean_dec(v_a_5804_);
lean_dec_ref(v_a_5803_);
lean_dec(v_a_5802_);
lean_dec_ref(v_a_5801_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5810_);
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5812_){
_start:
{
lean_object* v_res_5813_; 
v_res_5813_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_){
_start:
{
lean_object* v___x_5824_; 
v___x_5824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_){
_start:
{
lean_object* v_res_5835_; 
v_res_5835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
lean_dec(v___y_5833_);
lean_dec_ref(v___y_5832_);
lean_dec(v___y_5831_);
lean_dec_ref(v___y_5830_);
lean_dec(v___y_5829_);
lean_dec_ref(v___y_5828_);
lean_dec(v___y_5827_);
lean_dec_ref(v___y_5826_);
return v_res_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
lean_object* v___x_5846_; 
lean_inc(v___y_5840_);
lean_inc_ref(v___y_5839_);
lean_inc(v___y_5838_);
lean_inc_ref(v___y_5837_);
v___x_5846_ = lean_apply_9(v_x_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, lean_box(0));
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
return v_res_5857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5858_, lean_object* v_x_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_){
_start:
{
lean_object* v___f_5869_; lean_object* v___x_5870_; 
lean_inc(v___y_5863_);
lean_inc_ref(v___y_5862_);
lean_inc(v___y_5861_);
lean_inc_ref(v___y_5860_);
v___f_5869_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5869_, 0, v_x_5859_);
lean_closure_set(v___f_5869_, 1, v___y_5860_);
lean_closure_set(v___f_5869_, 2, v___y_5861_);
lean_closure_set(v___f_5869_, 3, v___y_5862_);
lean_closure_set(v___f_5869_, 4, v___y_5863_);
v___x_5870_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5858_, v___f_5869_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
if (lean_obj_tag(v___x_5870_) == 0)
{
return v___x_5870_;
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
v_a_5871_ = lean_ctor_get(v___x_5870_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5870_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5870_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5870_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5879_, lean_object* v_x_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_){
_start:
{
lean_object* v_res_5890_; 
v_res_5890_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5879_, v_x_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec(v___y_5884_);
lean_dec_ref(v___y_5883_);
lean_dec(v___y_5882_);
lean_dec_ref(v___y_5881_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5891_, lean_object* v_mvarId_5892_, lean_object* v_x_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_){
_start:
{
lean_object* v___x_5903_; 
v___x_5903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5892_, v_x_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
return v___x_5903_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5904_, lean_object* v_mvarId_5905_, lean_object* v_x_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_){
_start:
{
lean_object* v_res_5916_; 
v_res_5916_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5904_, v_mvarId_5905_, v_x_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_);
lean_dec(v___y_5914_);
lean_dec_ref(v___y_5913_);
lean_dec(v___y_5912_);
lean_dec_ref(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec_ref(v___y_5909_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
return v_res_5916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5917_, lean_object* v_pat_5918_, lean_object* v_a_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_){
_start:
{
lean_object* v___x_5929_; 
v___x_5929_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5917_, v_pat_5918_, v_a_5919_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_);
if (lean_obj_tag(v___x_5929_) == 0)
{
lean_object* v_a_5930_; lean_object* v___x_5931_; 
v_a_5930_ = lean_ctor_get(v___x_5929_, 0);
lean_inc(v_a_5930_);
lean_dec_ref_known(v___x_5929_, 1);
v___x_5931_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5930_, v___y_5921_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_);
return v___x_5931_;
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5939_; 
v_a_5932_ = lean_ctor_get(v___x_5929_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5934_ = v___x_5929_;
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5929_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5937_; 
if (v_isShared_5935_ == 0)
{
v___x_5937_ = v___x_5934_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
return v___x_5937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5940_, lean_object* v_pat_5941_, lean_object* v_a_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5940_, v_pat_5941_, v_a_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec(v___y_5946_);
lean_dec_ref(v___y_5945_);
lean_dec(v___y_5944_);
lean_dec_ref(v___y_5943_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5953_, size_t v_i_5954_, lean_object* v_bs_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
uint8_t v___x_5960_; 
v___x_5960_ = lean_usize_dec_lt(v_i_5954_, v_sz_5953_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5961_; 
v___x_5961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5961_, 0, v_bs_5955_);
return v___x_5961_;
}
else
{
lean_object* v_v_5962_; lean_object* v___x_5963_; 
v_v_5962_ = lean_array_uget_borrowed(v_bs_5955_, v_i_5954_);
lean_inc(v_v_5962_);
v___x_5963_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_5962_, v___y_5956_, v___y_5957_, v___y_5958_);
if (lean_obj_tag(v___x_5963_) == 0)
{
lean_object* v_a_5964_; lean_object* v_hIdent_x3f_5965_; lean_object* v_term_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5979_; 
v_a_5964_ = lean_ctor_get(v___x_5963_, 0);
lean_inc(v_a_5964_);
lean_dec_ref_known(v___x_5963_, 1);
v_hIdent_x3f_5965_ = lean_ctor_get(v_a_5964_, 0);
v_term_5966_ = lean_ctor_get(v_a_5964_, 1);
v_isSharedCheck_5979_ = !lean_is_exclusive(v_a_5964_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5968_ = v_a_5964_;
v_isShared_5969_ = v_isSharedCheck_5979_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_term_5966_);
lean_inc(v_hIdent_x3f_5965_);
lean_dec(v_a_5964_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5979_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5970_; lean_object* v_bs_x27_5971_; lean_object* v___x_5973_; 
v___x_5970_ = lean_unsigned_to_nat(0u);
v_bs_x27_5971_ = lean_array_uset(v_bs_5955_, v_i_5954_, v___x_5970_);
if (v_isShared_5969_ == 0)
{
v___x_5973_ = v___x_5968_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_hIdent_x3f_5965_);
lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_term_5966_);
v___x_5973_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
size_t v___x_5974_; size_t v___x_5975_; lean_object* v___x_5976_; 
v___x_5974_ = ((size_t)1ULL);
v___x_5975_ = lean_usize_add(v_i_5954_, v___x_5974_);
v___x_5976_ = lean_array_uset(v_bs_x27_5971_, v_i_5954_, v___x_5973_);
v_i_5954_ = v___x_5975_;
v_bs_5955_ = v___x_5976_;
goto _start;
}
}
}
else
{
lean_object* v_a_5980_; lean_object* v___x_5982_; uint8_t v_isShared_5983_; uint8_t v_isSharedCheck_5987_; 
lean_dec_ref(v_bs_5955_);
v_a_5980_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_5987_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_5987_ == 0)
{
v___x_5982_ = v___x_5963_;
v_isShared_5983_ = v_isSharedCheck_5987_;
goto v_resetjp_5981_;
}
else
{
lean_inc(v_a_5980_);
lean_dec(v___x_5963_);
v___x_5982_ = lean_box(0);
v_isShared_5983_ = v_isSharedCheck_5987_;
goto v_resetjp_5981_;
}
v_resetjp_5981_:
{
lean_object* v___x_5985_; 
if (v_isShared_5983_ == 0)
{
v___x_5985_ = v___x_5982_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5986_; 
v_reuseFailAlloc_5986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5986_, 0, v_a_5980_);
v___x_5985_ = v_reuseFailAlloc_5986_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
return v___x_5985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_5988_, lean_object* v_i_5989_, lean_object* v_bs_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_){
_start:
{
size_t v_sz_boxed_5995_; size_t v_i_boxed_5996_; lean_object* v_res_5997_; 
v_sz_boxed_5995_ = lean_unbox_usize(v_sz_5988_);
lean_dec(v_sz_5988_);
v_i_boxed_5996_ = lean_unbox_usize(v_i_5989_);
lean_dec(v_i_5989_);
v_res_5997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_5995_, v_i_boxed_5996_, v_bs_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
lean_dec(v___y_5993_);
lean_dec_ref(v___y_5992_);
lean_dec_ref(v___y_5991_);
return v_res_5997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_){
_start:
{
lean_object* v___y_6015_; lean_object* v_pat_6016_; lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6019_; lean_object* v___y_6020_; lean_object* v___y_6021_; lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___x_6050_; uint8_t v___x_6051_; 
v___x_6050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_6004_);
v___x_6051_ = l_Lean_Syntax_isOfKind(v_stx_6004_, v___x_6050_);
if (v___x_6051_ == 0)
{
lean_object* v___x_6052_; 
lean_dec(v_stx_6004_);
v___x_6052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6052_;
}
else
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; uint8_t v___x_6057_; 
v___x_6053_ = lean_unsigned_to_nat(1u);
v___x_6054_ = l_Lean_Syntax_getArg(v_stx_6004_, v___x_6053_);
v___x_6055_ = lean_unsigned_to_nat(2u);
v___x_6056_ = l_Lean_Syntax_getArg(v_stx_6004_, v___x_6055_);
v___x_6057_ = l_Lean_Syntax_isNone(v___x_6056_);
if (v___x_6057_ == 0)
{
uint8_t v___x_6058_; 
lean_dec(v_stx_6004_);
lean_inc(v___x_6056_);
v___x_6058_ = l_Lean_Syntax_matchesNull(v___x_6056_, v___x_6055_);
if (v___x_6058_ == 0)
{
lean_object* v___x_6059_; 
lean_dec(v___x_6056_);
lean_dec(v___x_6054_);
v___x_6059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6059_;
}
else
{
lean_object* v_pat_x3f_6060_; lean_object* v___x_6061_; 
v_pat_x3f_6060_ = l_Lean_Syntax_getArg(v___x_6056_, v___x_6053_);
lean_dec(v___x_6056_);
v___x_6061_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6060_, v_a_6009_, v_a_6010_, v_a_6011_, v_a_6012_);
if (lean_obj_tag(v___x_6061_) == 0)
{
lean_object* v_a_6062_; lean_object* v_tgts_6063_; 
v_a_6062_ = lean_ctor_get(v___x_6061_, 0);
lean_inc(v_a_6062_);
lean_dec_ref_known(v___x_6061_, 1);
v_tgts_6063_ = l_Lean_Syntax_getArgs(v___x_6054_);
lean_dec(v___x_6054_);
v___y_6015_ = v_tgts_6063_;
v_pat_6016_ = v_a_6062_;
v___y_6017_ = v_a_6005_;
v___y_6018_ = v_a_6006_;
v___y_6019_ = v_a_6007_;
v___y_6020_ = v_a_6008_;
v___y_6021_ = v_a_6009_;
v___y_6022_ = v_a_6010_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
goto v___jp_6014_;
}
else
{
lean_object* v_a_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6071_; 
lean_dec(v___x_6054_);
v_a_6064_ = lean_ctor_get(v___x_6061_, 0);
v_isSharedCheck_6071_ = !lean_is_exclusive(v___x_6061_);
if (v_isSharedCheck_6071_ == 0)
{
v___x_6066_ = v___x_6061_;
v_isShared_6067_ = v_isSharedCheck_6071_;
goto v_resetjp_6065_;
}
else
{
lean_inc(v_a_6064_);
lean_dec(v___x_6061_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6071_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v___x_6069_; 
if (v_isShared_6067_ == 0)
{
v___x_6069_ = v___x_6066_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v_a_6064_);
v___x_6069_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
return v___x_6069_;
}
}
}
}
}
else
{
lean_object* v___x_6072_; lean_object* v_tk_6073_; lean_object* v_tgts_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
lean_dec(v___x_6056_);
v___x_6072_ = lean_unsigned_to_nat(0u);
v_tk_6073_ = l_Lean_Syntax_getArg(v_stx_6004_, v___x_6072_);
lean_dec(v_stx_6004_);
v_tgts_6074_ = l_Lean_Syntax_getArgs(v___x_6054_);
lean_dec(v___x_6054_);
v___x_6075_ = lean_box(0);
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v_tk_6073_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___y_6015_ = v_tgts_6074_;
v_pat_6016_ = v___x_6076_;
v___y_6017_ = v_a_6005_;
v___y_6018_ = v_a_6006_;
v___y_6019_ = v_a_6007_;
v___y_6020_ = v_a_6008_;
v___y_6021_ = v_a_6009_;
v___y_6022_ = v_a_6010_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
goto v___jp_6014_;
}
}
v___jp_6014_:
{
lean_object* v___x_6025_; size_t v_sz_6026_; size_t v___x_6027_; lean_object* v___x_6028_; 
v___x_6025_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6015_);
lean_dec_ref(v___y_6015_);
v_sz_6026_ = lean_array_size(v___x_6025_);
v___x_6027_ = ((size_t)0ULL);
v___x_6028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6026_, v___x_6027_, v___x_6025_, v___y_6021_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; lean_object* v___x_6030_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
lean_inc(v_a_6029_);
lean_dec_ref_known(v___x_6028_, 1);
v___x_6030_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6018_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6030_) == 0)
{
lean_object* v_a_6031_; lean_object* v___f_6032_; lean_object* v___x_6033_; 
v_a_6031_ = lean_ctor_get(v___x_6030_, 0);
lean_inc_n(v_a_6031_, 2);
lean_dec_ref_known(v___x_6030_, 1);
v___f_6032_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6032_, 0, v_a_6029_);
lean_closure_set(v___f_6032_, 1, v_pat_6016_);
lean_closure_set(v___f_6032_, 2, v_a_6031_);
v___x_6033_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6031_, v___f_6032_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
return v___x_6033_;
}
else
{
lean_object* v_a_6034_; lean_object* v___x_6036_; uint8_t v_isShared_6037_; uint8_t v_isSharedCheck_6041_; 
lean_dec(v_a_6029_);
lean_dec_ref(v_pat_6016_);
v_a_6034_ = lean_ctor_get(v___x_6030_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_6030_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_6036_ = v___x_6030_;
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
else
{
lean_inc(v_a_6034_);
lean_dec(v___x_6030_);
v___x_6036_ = lean_box(0);
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
v_resetjp_6035_:
{
lean_object* v___x_6039_; 
if (v_isShared_6037_ == 0)
{
v___x_6039_ = v___x_6036_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v_a_6034_);
v___x_6039_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
return v___x_6039_;
}
}
}
}
else
{
lean_object* v_a_6042_; lean_object* v___x_6044_; uint8_t v_isShared_6045_; uint8_t v_isSharedCheck_6049_; 
lean_dec_ref(v_pat_6016_);
v_a_6042_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_6044_ = v___x_6028_;
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
else
{
lean_inc(v_a_6042_);
lean_dec(v___x_6028_);
v___x_6044_ = lean_box(0);
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
v_resetjp_6043_:
{
lean_object* v___x_6047_; 
if (v_isShared_6045_ == 0)
{
v___x_6047_ = v___x_6044_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6042_);
v___x_6047_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
return v___x_6047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6077_, lean_object* v_a_6078_, lean_object* v_a_6079_, lean_object* v_a_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6077_, v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
lean_dec(v_a_6085_);
lean_dec_ref(v_a_6084_);
lean_dec(v_a_6083_);
lean_dec_ref(v_a_6082_);
lean_dec(v_a_6081_);
lean_dec_ref(v_a_6080_);
lean_dec(v_a_6079_);
lean_dec_ref(v_a_6078_);
return v_res_6087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6088_, size_t v_i_6089_, lean_object* v_bs_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_){
_start:
{
lean_object* v___x_6100_; 
v___x_6100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6088_, v_i_6089_, v_bs_6090_, v___y_6095_, v___y_6097_, v___y_6098_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6101_, lean_object* v_i_6102_, lean_object* v_bs_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
size_t v_sz_boxed_6113_; size_t v_i_boxed_6114_; lean_object* v_res_6115_; 
v_sz_boxed_6113_ = lean_unbox_usize(v_sz_6101_);
lean_dec(v_sz_6101_);
v_i_boxed_6114_ = lean_unbox_usize(v_i_6102_);
lean_dec(v_i_6102_);
v_res_6115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6113_, v_i_boxed_6114_, v_bs_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6108_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6152_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6155_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6156_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6152_, v___x_6153_, v___x_6154_, v___x_6155_);
return v___x_6156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6159_, lean_object* v___x_6160_, lean_object* v_a_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v___x_6171_; 
v___x_6171_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6159_, v___x_6160_, v_a_6161_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
if (lean_obj_tag(v___x_6171_) == 0)
{
lean_object* v_a_6172_; lean_object* v___x_6173_; 
v_a_6172_ = lean_ctor_get(v___x_6171_, 0);
lean_inc(v_a_6172_);
lean_dec_ref_known(v___x_6171_, 1);
v___x_6173_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6172_, v___y_6163_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
return v___x_6173_;
}
else
{
lean_object* v_a_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6181_; 
v_a_6174_ = lean_ctor_get(v___x_6171_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6176_ = v___x_6171_;
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_a_6174_);
lean_dec(v___x_6171_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6179_; 
if (v_isShared_6177_ == 0)
{
v___x_6179_ = v___x_6176_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
v___x_6179_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
return v___x_6179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6182_, lean_object* v___x_6183_, lean_object* v_a_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6182_, v___x_6183_, v_a_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec(v___y_6186_);
lean_dec_ref(v___y_6185_);
return v_res_6194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6195_, lean_object* v_val_6196_, lean_object* v_a_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
lean_object* v___x_6207_; 
v___x_6207_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6195_, v_val_6196_, v_a_6197_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
if (lean_obj_tag(v___x_6207_) == 0)
{
lean_object* v_a_6208_; lean_object* v___x_6209_; 
v_a_6208_ = lean_ctor_get(v___x_6207_, 0);
lean_inc(v_a_6208_);
lean_dec_ref_known(v___x_6207_, 1);
v___x_6209_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6208_, v___y_6199_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
return v___x_6209_;
}
else
{
lean_object* v_a_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6217_; 
v_a_6210_ = lean_ctor_get(v___x_6207_, 0);
v_isSharedCheck_6217_ = !lean_is_exclusive(v___x_6207_);
if (v_isSharedCheck_6217_ == 0)
{
v___x_6212_ = v___x_6207_;
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_a_6210_);
lean_dec(v___x_6207_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6215_; 
if (v_isShared_6213_ == 0)
{
v___x_6215_ = v___x_6212_;
goto v_reusejp_6214_;
}
else
{
lean_object* v_reuseFailAlloc_6216_; 
v_reuseFailAlloc_6216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
v___x_6215_ = v_reuseFailAlloc_6216_;
goto v_reusejp_6214_;
}
v_reusejp_6214_:
{
return v___x_6215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6218_, lean_object* v_val_6219_, lean_object* v_a_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_){
_start:
{
lean_object* v_res_6230_; 
v_res_6230_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6218_, v_val_6219_, v_a_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
lean_dec(v___y_6224_);
lean_dec_ref(v___y_6223_);
lean_dec(v___y_6222_);
lean_dec_ref(v___y_6221_);
return v_res_6230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
lean_object* v_ref_6237_; lean_object* v___x_6238_; lean_object* v_a_6239_; lean_object* v___x_6241_; uint8_t v_isShared_6242_; uint8_t v_isSharedCheck_6247_; 
v_ref_6237_ = lean_ctor_get(v___y_6234_, 2);
v___x_6238_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_);
v_a_6239_ = lean_ctor_get(v___x_6238_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v___x_6238_);
if (v_isSharedCheck_6247_ == 0)
{
v___x_6241_ = v___x_6238_;
v_isShared_6242_ = v_isSharedCheck_6247_;
goto v_resetjp_6240_;
}
else
{
lean_inc(v_a_6239_);
lean_dec(v___x_6238_);
v___x_6241_ = lean_box(0);
v_isShared_6242_ = v_isSharedCheck_6247_;
goto v_resetjp_6240_;
}
v_resetjp_6240_:
{
lean_object* v___x_6243_; lean_object* v___x_6245_; 
lean_inc(v_ref_6237_);
v___x_6243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6243_, 0, v_ref_6237_);
lean_ctor_set(v___x_6243_, 1, v_a_6239_);
if (v_isShared_6242_ == 0)
{
lean_ctor_set_tag(v___x_6241_, 1);
lean_ctor_set(v___x_6241_, 0, v___x_6243_);
v___x_6245_ = v___x_6241_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6246_; 
v_reuseFailAlloc_6246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6246_, 0, v___x_6243_);
v___x_6245_ = v_reuseFailAlloc_6246_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
return v___x_6245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_){
_start:
{
lean_object* v_res_6254_; 
v_res_6254_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
lean_dec(v___y_6252_);
lean_dec_ref(v___y_6251_);
lean_dec(v___y_6250_);
lean_dec_ref(v___y_6249_);
return v_res_6254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6255_, size_t v_i_6256_, lean_object* v_bs_6257_){
_start:
{
uint8_t v___x_6258_; 
v___x_6258_ = lean_usize_dec_lt(v_i_6256_, v_sz_6255_);
if (v___x_6258_ == 0)
{
return v_bs_6257_;
}
else
{
lean_object* v_v_6259_; lean_object* v___x_6260_; lean_object* v_bs_x27_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; size_t v___x_6264_; size_t v___x_6265_; lean_object* v___x_6266_; 
v_v_6259_ = lean_array_uget(v_bs_6257_, v_i_6256_);
v___x_6260_ = lean_unsigned_to_nat(0u);
v_bs_x27_6261_ = lean_array_uset(v_bs_6257_, v_i_6256_, v___x_6260_);
v___x_6262_ = lean_box(0);
v___x_6263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6263_, 0, v___x_6262_);
lean_ctor_set(v___x_6263_, 1, v_v_6259_);
v___x_6264_ = ((size_t)1ULL);
v___x_6265_ = lean_usize_add(v_i_6256_, v___x_6264_);
v___x_6266_ = lean_array_uset(v_bs_x27_6261_, v_i_6256_, v___x_6263_);
v_i_6256_ = v___x_6265_;
v_bs_6257_ = v___x_6266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6268_, lean_object* v_i_6269_, lean_object* v_bs_6270_){
_start:
{
size_t v_sz_boxed_6271_; size_t v_i_boxed_6272_; lean_object* v_res_6273_; 
v_sz_boxed_6271_ = lean_unbox_usize(v_sz_6268_);
lean_dec(v_sz_6268_);
v_i_boxed_6272_ = lean_unbox_usize(v_i_6269_);
lean_dec(v_i_6269_);
v_res_6273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6271_, v_i_boxed_6272_, v_bs_6270_);
return v_res_6273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6285_ = l_Lean_stringToMessageData(v___x_6284_);
return v___x_6285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6286_, lean_object* v_a_6287_, lean_object* v_a_6288_, lean_object* v_a_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_){
_start:
{
lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; lean_object* v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___x_6319_; uint8_t v___x_6320_; 
v___x_6319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6286_);
v___x_6320_ = l_Lean_Syntax_isOfKind(v_stx_6286_, v___x_6319_);
if (v___x_6320_ == 0)
{
lean_object* v___x_6321_; 
lean_dec(v_stx_6286_);
v___x_6321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6321_;
}
else
{
lean_object* v___x_6322_; lean_object* v_tk_6323_; lean_object* v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v_a_6364_; lean_object* v___y_6378_; lean_object* v___y_6379_; lean_object* v_val_x3f_6380_; lean_object* v___y_6381_; lean_object* v___y_6382_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___x_6408_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v_ty_x3f_6412_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v_pat_x3f_6431_; lean_object* v___y_6432_; lean_object* v___y_6433_; lean_object* v___y_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; lean_object* v___y_6437_; lean_object* v___y_6438_; lean_object* v___y_6439_; lean_object* v___x_6448_; uint8_t v___x_6449_; 
v___x_6322_ = lean_unsigned_to_nat(0u);
v_tk_6323_ = l_Lean_Syntax_getArg(v_stx_6286_, v___x_6322_);
v___x_6408_ = lean_unsigned_to_nat(1u);
v___x_6448_ = l_Lean_Syntax_getArg(v_stx_6286_, v___x_6408_);
v___x_6449_ = l_Lean_Syntax_isNone(v___x_6448_);
if (v___x_6449_ == 0)
{
uint8_t v___x_6450_; 
lean_inc(v___x_6448_);
v___x_6450_ = l_Lean_Syntax_matchesNull(v___x_6448_, v___x_6408_);
if (v___x_6450_ == 0)
{
lean_object* v___x_6451_; 
lean_dec(v___x_6448_);
lean_dec(v_tk_6323_);
lean_dec(v_stx_6286_);
v___x_6451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6451_;
}
else
{
lean_object* v_pat_x3f_6452_; 
v_pat_x3f_6452_ = l_Lean_Syntax_getArg(v___x_6448_, v___x_6322_);
lean_dec(v___x_6448_);
if (v___x_6449_ == 0)
{
lean_object* v___x_6455_; uint8_t v___x_6456_; 
v___x_6455_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6452_);
v___x_6456_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6452_, v___x_6455_);
if (v___x_6456_ == 0)
{
lean_object* v___x_6457_; 
lean_dec(v_pat_x3f_6452_);
lean_dec(v_tk_6323_);
lean_dec(v_stx_6286_);
v___x_6457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6457_;
}
else
{
goto v___jp_6453_;
}
}
else
{
goto v___jp_6453_;
}
v___jp_6453_:
{
lean_object* v___x_6454_; 
v___x_6454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6454_, 0, v_pat_x3f_6452_);
v_pat_x3f_6431_ = v___x_6454_;
v___y_6432_ = v_a_6287_;
v___y_6433_ = v_a_6288_;
v___y_6434_ = v_a_6289_;
v___y_6435_ = v_a_6290_;
v___y_6436_ = v_a_6291_;
v___y_6437_ = v_a_6292_;
v___y_6438_ = v_a_6293_;
v___y_6439_ = v_a_6294_;
goto v___jp_6430_;
}
}
}
else
{
lean_object* v___x_6458_; 
lean_dec(v___x_6448_);
v___x_6458_ = lean_box(0);
v_pat_x3f_6431_ = v___x_6458_;
v___y_6432_ = v_a_6287_;
v___y_6433_ = v_a_6288_;
v___y_6434_ = v_a_6289_;
v___y_6435_ = v_a_6290_;
v___y_6436_ = v_a_6291_;
v___y_6437_ = v_a_6292_;
v___y_6438_ = v_a_6293_;
v___y_6439_ = v_a_6294_;
goto v___jp_6430_;
}
v___jp_6324_:
{
lean_object* v___x_6336_; 
v___x_6336_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6330_, v___y_6329_, v___y_6327_, v___y_6332_, v___y_6328_);
if (lean_obj_tag(v___x_6336_) == 0)
{
lean_object* v_a_6337_; lean_object* v___x_6338_; size_t v_sz_6339_; lean_object* v___x_6340_; size_t v___x_6341_; lean_object* v___x_6342_; lean_object* v___f_6343_; lean_object* v___x_6344_; 
v_a_6337_ = lean_ctor_get(v___x_6336_, 0);
lean_inc_n(v_a_6337_, 2);
lean_dec_ref_known(v___x_6336_, 1);
v___x_6338_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6333_);
lean_dec_ref(v___y_6333_);
v_sz_6339_ = lean_array_size(v___x_6338_);
v___x_6340_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6323_, v___y_6335_, v___y_6334_);
lean_dec(v___y_6334_);
v___x_6341_ = ((size_t)0ULL);
v___x_6342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6339_, v___x_6341_, v___x_6338_);
v___f_6343_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6343_, 0, v___x_6342_);
lean_closure_set(v___f_6343_, 1, v___x_6340_);
lean_closure_set(v___f_6343_, 2, v_a_6337_);
v___x_6344_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6337_, v___f_6343_, v___y_6326_, v___y_6330_, v___y_6331_, v___y_6325_, v___y_6329_, v___y_6327_, v___y_6332_, v___y_6328_);
return v___x_6344_;
}
else
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6352_; 
lean_dec_ref(v___y_6335_);
lean_dec(v___y_6334_);
lean_dec_ref(v___y_6333_);
lean_dec(v_tk_6323_);
v_a_6345_ = lean_ctor_get(v___x_6336_, 0);
v_isSharedCheck_6352_ = !lean_is_exclusive(v___x_6336_);
if (v_isSharedCheck_6352_ == 0)
{
v___x_6347_ = v___x_6336_;
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v___x_6336_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
lean_object* v___x_6350_; 
if (v_isShared_6348_ == 0)
{
v___x_6350_ = v___x_6347_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6351_; 
v_reuseFailAlloc_6351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6351_, 0, v_a_6345_);
v___x_6350_ = v_reuseFailAlloc_6351_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
return v___x_6350_;
}
}
}
}
v___jp_6353_:
{
if (lean_obj_tag(v___y_6362_) == 1)
{
if (lean_obj_tag(v_a_6364_) == 0)
{
lean_object* v_val_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v_val_6365_ = lean_ctor_get(v___y_6362_, 0);
lean_inc(v_val_6365_);
lean_dec_ref_known(v___y_6362_, 1);
v___x_6366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6323_);
v___x_6367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6367_, 0, v_tk_6323_);
lean_ctor_set(v___x_6367_, 1, v___x_6366_);
v___y_6325_ = v___y_6354_;
v___y_6326_ = v___y_6356_;
v___y_6327_ = v___y_6355_;
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6359_;
v___y_6330_ = v___y_6358_;
v___y_6331_ = v___y_6361_;
v___y_6332_ = v___y_6360_;
v___y_6333_ = v_val_6365_;
v___y_6334_ = v___y_6363_;
v___y_6335_ = v___x_6367_;
goto v___jp_6324_;
}
else
{
lean_object* v_val_6368_; lean_object* v_val_6369_; 
v_val_6368_ = lean_ctor_get(v___y_6362_, 0);
lean_inc(v_val_6368_);
lean_dec_ref_known(v___y_6362_, 1);
v_val_6369_ = lean_ctor_get(v_a_6364_, 0);
lean_inc(v_val_6369_);
lean_dec_ref_known(v_a_6364_, 1);
v___y_6325_ = v___y_6354_;
v___y_6326_ = v___y_6356_;
v___y_6327_ = v___y_6355_;
v___y_6328_ = v___y_6357_;
v___y_6329_ = v___y_6359_;
v___y_6330_ = v___y_6358_;
v___y_6331_ = v___y_6361_;
v___y_6332_ = v___y_6360_;
v___y_6333_ = v_val_6368_;
v___y_6334_ = v___y_6363_;
v___y_6335_ = v_val_6369_;
goto v___jp_6324_;
}
}
else
{
lean_dec(v___y_6362_);
if (lean_obj_tag(v___y_6363_) == 1)
{
if (lean_obj_tag(v_a_6364_) == 0)
{
lean_object* v_val_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; 
v_val_6370_ = lean_ctor_get(v___y_6363_, 0);
lean_inc(v_val_6370_);
lean_dec_ref_known(v___y_6363_, 1);
v___x_6371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6372_, 0, v_tk_6323_);
lean_ctor_set(v___x_6372_, 1, v___x_6371_);
v___y_6297_ = v_val_6370_;
v___y_6298_ = v___y_6354_;
v___y_6299_ = v___y_6356_;
v___y_6300_ = v___y_6355_;
v___y_6301_ = v___y_6357_;
v___y_6302_ = v___y_6359_;
v___y_6303_ = v___y_6358_;
v___y_6304_ = v___y_6361_;
v___y_6305_ = v___y_6360_;
v___y_6306_ = v___x_6372_;
goto v___jp_6296_;
}
else
{
lean_object* v_val_6373_; lean_object* v_val_6374_; 
lean_dec(v_tk_6323_);
v_val_6373_ = lean_ctor_get(v___y_6363_, 0);
lean_inc(v_val_6373_);
lean_dec_ref_known(v___y_6363_, 1);
v_val_6374_ = lean_ctor_get(v_a_6364_, 0);
lean_inc(v_val_6374_);
lean_dec_ref_known(v_a_6364_, 1);
v___y_6297_ = v_val_6373_;
v___y_6298_ = v___y_6354_;
v___y_6299_ = v___y_6356_;
v___y_6300_ = v___y_6355_;
v___y_6301_ = v___y_6357_;
v___y_6302_ = v___y_6359_;
v___y_6303_ = v___y_6358_;
v___y_6304_ = v___y_6361_;
v___y_6305_ = v___y_6360_;
v___y_6306_ = v_val_6374_;
goto v___jp_6296_;
}
}
else
{
lean_object* v___x_6375_; lean_object* v___x_6376_; 
lean_dec(v_a_6364_);
lean_dec(v___y_6363_);
lean_dec(v_tk_6323_);
v___x_6375_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6376_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6375_, v___y_6359_, v___y_6355_, v___y_6360_, v___y_6357_);
return v___x_6376_;
}
}
}
v___jp_6377_:
{
if (lean_obj_tag(v___y_6378_) == 0)
{
lean_object* v___x_6389_; 
v___x_6389_ = lean_box(0);
v___y_6354_ = v___y_6384_;
v___y_6355_ = v___y_6386_;
v___y_6356_ = v___y_6381_;
v___y_6357_ = v___y_6388_;
v___y_6358_ = v___y_6382_;
v___y_6359_ = v___y_6385_;
v___y_6360_ = v___y_6387_;
v___y_6361_ = v___y_6383_;
v___y_6362_ = v_val_x3f_6380_;
v___y_6363_ = v___y_6379_;
v_a_6364_ = v___x_6389_;
goto v___jp_6353_;
}
else
{
lean_object* v_val_6390_; lean_object* v___x_6392_; uint8_t v_isShared_6393_; uint8_t v_isSharedCheck_6407_; 
v_val_6390_ = lean_ctor_get(v___y_6378_, 0);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___y_6378_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6392_ = v___y_6378_;
v_isShared_6393_ = v_isSharedCheck_6407_;
goto v_resetjp_6391_;
}
else
{
lean_inc(v_val_6390_);
lean_dec(v___y_6378_);
v___x_6392_ = lean_box(0);
v_isShared_6393_ = v_isSharedCheck_6407_;
goto v_resetjp_6391_;
}
v_resetjp_6391_:
{
lean_object* v___x_6394_; 
v___x_6394_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6390_, v___y_6385_, v___y_6386_, v___y_6387_, v___y_6388_);
if (lean_obj_tag(v___x_6394_) == 0)
{
lean_object* v_a_6395_; lean_object* v___x_6397_; 
v_a_6395_ = lean_ctor_get(v___x_6394_, 0);
lean_inc(v_a_6395_);
lean_dec_ref_known(v___x_6394_, 1);
if (v_isShared_6393_ == 0)
{
lean_ctor_set(v___x_6392_, 0, v_a_6395_);
v___x_6397_ = v___x_6392_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6398_; 
v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6395_);
v___x_6397_ = v_reuseFailAlloc_6398_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
v___y_6354_ = v___y_6384_;
v___y_6355_ = v___y_6386_;
v___y_6356_ = v___y_6381_;
v___y_6357_ = v___y_6388_;
v___y_6358_ = v___y_6382_;
v___y_6359_ = v___y_6385_;
v___y_6360_ = v___y_6387_;
v___y_6361_ = v___y_6383_;
v___y_6362_ = v_val_x3f_6380_;
v___y_6363_ = v___y_6379_;
v_a_6364_ = v___x_6397_;
goto v___jp_6353_;
}
}
else
{
lean_object* v_a_6399_; lean_object* v___x_6401_; uint8_t v_isShared_6402_; uint8_t v_isSharedCheck_6406_; 
lean_del_object(v___x_6392_);
lean_dec(v_val_x3f_6380_);
lean_dec(v___y_6379_);
lean_dec(v_tk_6323_);
v_a_6399_ = lean_ctor_get(v___x_6394_, 0);
v_isSharedCheck_6406_ = !lean_is_exclusive(v___x_6394_);
if (v_isSharedCheck_6406_ == 0)
{
v___x_6401_ = v___x_6394_;
v_isShared_6402_ = v_isSharedCheck_6406_;
goto v_resetjp_6400_;
}
else
{
lean_inc(v_a_6399_);
lean_dec(v___x_6394_);
v___x_6401_ = lean_box(0);
v_isShared_6402_ = v_isSharedCheck_6406_;
goto v_resetjp_6400_;
}
v_resetjp_6400_:
{
lean_object* v___x_6404_; 
if (v_isShared_6402_ == 0)
{
v___x_6404_ = v___x_6401_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_a_6399_);
v___x_6404_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
return v___x_6404_;
}
}
}
}
}
}
v___jp_6409_:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; uint8_t v___x_6423_; 
v___x_6421_ = lean_unsigned_to_nat(3u);
v___x_6422_ = l_Lean_Syntax_getArg(v_stx_6286_, v___x_6421_);
lean_dec(v_stx_6286_);
v___x_6423_ = l_Lean_Syntax_isNone(v___x_6422_);
if (v___x_6423_ == 0)
{
uint8_t v___x_6424_; 
lean_inc(v___x_6422_);
v___x_6424_ = l_Lean_Syntax_matchesNull(v___x_6422_, v___y_6411_);
if (v___x_6424_ == 0)
{
lean_object* v___x_6425_; 
lean_dec(v___x_6422_);
lean_dec(v_ty_x3f_6412_);
lean_dec(v___y_6410_);
lean_dec(v_tk_6323_);
v___x_6425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6425_;
}
else
{
lean_object* v___x_6426_; lean_object* v_val_x3f_6427_; lean_object* v___x_6428_; 
v___x_6426_ = l_Lean_Syntax_getArg(v___x_6422_, v___x_6408_);
lean_dec(v___x_6422_);
v_val_x3f_6427_ = l_Lean_Syntax_getArgs(v___x_6426_);
lean_dec(v___x_6426_);
v___x_6428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6428_, 0, v_val_x3f_6427_);
v___y_6378_ = v___y_6410_;
v___y_6379_ = v_ty_x3f_6412_;
v_val_x3f_6380_ = v___x_6428_;
v___y_6381_ = v___y_6413_;
v___y_6382_ = v___y_6414_;
v___y_6383_ = v___y_6415_;
v___y_6384_ = v___y_6416_;
v___y_6385_ = v___y_6417_;
v___y_6386_ = v___y_6418_;
v___y_6387_ = v___y_6419_;
v___y_6388_ = v___y_6420_;
goto v___jp_6377_;
}
}
else
{
lean_object* v___x_6429_; 
lean_dec(v___x_6422_);
v___x_6429_ = lean_box(0);
v___y_6378_ = v___y_6410_;
v___y_6379_ = v_ty_x3f_6412_;
v_val_x3f_6380_ = v___x_6429_;
v___y_6381_ = v___y_6413_;
v___y_6382_ = v___y_6414_;
v___y_6383_ = v___y_6415_;
v___y_6384_ = v___y_6416_;
v___y_6385_ = v___y_6417_;
v___y_6386_ = v___y_6418_;
v___y_6387_ = v___y_6419_;
v___y_6388_ = v___y_6420_;
goto v___jp_6377_;
}
}
v___jp_6430_:
{
lean_object* v___x_6440_; lean_object* v___x_6441_; uint8_t v___x_6442_; 
v___x_6440_ = lean_unsigned_to_nat(2u);
v___x_6441_ = l_Lean_Syntax_getArg(v_stx_6286_, v___x_6440_);
v___x_6442_ = l_Lean_Syntax_isNone(v___x_6441_);
if (v___x_6442_ == 0)
{
uint8_t v___x_6443_; 
lean_inc(v___x_6441_);
v___x_6443_ = l_Lean_Syntax_matchesNull(v___x_6441_, v___x_6440_);
if (v___x_6443_ == 0)
{
lean_object* v___x_6444_; 
lean_dec(v___x_6441_);
lean_dec(v_pat_x3f_6431_);
lean_dec(v_tk_6323_);
lean_dec(v_stx_6286_);
v___x_6444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6444_;
}
else
{
lean_object* v_ty_x3f_6445_; lean_object* v___x_6446_; 
v_ty_x3f_6445_ = l_Lean_Syntax_getArg(v___x_6441_, v___x_6408_);
lean_dec(v___x_6441_);
v___x_6446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6446_, 0, v_ty_x3f_6445_);
v___y_6410_ = v_pat_x3f_6431_;
v___y_6411_ = v___x_6440_;
v_ty_x3f_6412_ = v___x_6446_;
v___y_6413_ = v___y_6432_;
v___y_6414_ = v___y_6433_;
v___y_6415_ = v___y_6434_;
v___y_6416_ = v___y_6435_;
v___y_6417_ = v___y_6436_;
v___y_6418_ = v___y_6437_;
v___y_6419_ = v___y_6438_;
v___y_6420_ = v___y_6439_;
goto v___jp_6409_;
}
}
else
{
lean_object* v___x_6447_; 
lean_dec(v___x_6441_);
v___x_6447_ = lean_box(0);
v___y_6410_ = v_pat_x3f_6431_;
v___y_6411_ = v___x_6440_;
v_ty_x3f_6412_ = v___x_6447_;
v___y_6413_ = v___y_6432_;
v___y_6414_ = v___y_6433_;
v___y_6415_ = v___y_6434_;
v___y_6416_ = v___y_6435_;
v___y_6417_ = v___y_6436_;
v___y_6418_ = v___y_6437_;
v___y_6419_ = v___y_6438_;
v___y_6420_ = v___y_6439_;
goto v___jp_6409_;
}
}
}
v___jp_6296_:
{
lean_object* v___x_6307_; 
v___x_6307_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6303_, v___y_6302_, v___y_6300_, v___y_6305_, v___y_6301_);
if (lean_obj_tag(v___x_6307_) == 0)
{
lean_object* v_a_6308_; lean_object* v___f_6309_; lean_object* v___x_6310_; 
v_a_6308_ = lean_ctor_get(v___x_6307_, 0);
lean_inc_n(v_a_6308_, 2);
lean_dec_ref_known(v___x_6307_, 1);
v___f_6309_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6309_, 0, v___y_6306_);
lean_closure_set(v___f_6309_, 1, v___y_6297_);
lean_closure_set(v___f_6309_, 2, v_a_6308_);
v___x_6310_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6308_, v___f_6309_, v___y_6299_, v___y_6303_, v___y_6304_, v___y_6298_, v___y_6302_, v___y_6300_, v___y_6305_, v___y_6301_);
return v___x_6310_;
}
else
{
lean_object* v_a_6311_; lean_object* v___x_6313_; uint8_t v_isShared_6314_; uint8_t v_isSharedCheck_6318_; 
lean_dec_ref(v___y_6306_);
lean_dec(v___y_6297_);
v_a_6311_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6318_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6318_ == 0)
{
v___x_6313_ = v___x_6307_;
v_isShared_6314_ = v_isSharedCheck_6318_;
goto v_resetjp_6312_;
}
else
{
lean_inc(v_a_6311_);
lean_dec(v___x_6307_);
v___x_6313_ = lean_box(0);
v_isShared_6314_ = v_isSharedCheck_6318_;
goto v_resetjp_6312_;
}
v_resetjp_6312_:
{
lean_object* v___x_6316_; 
if (v_isShared_6314_ == 0)
{
v___x_6316_ = v___x_6313_;
goto v_reusejp_6315_;
}
else
{
lean_object* v_reuseFailAlloc_6317_; 
v_reuseFailAlloc_6317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
v___x_6316_ = v_reuseFailAlloc_6317_;
goto v_reusejp_6315_;
}
v_reusejp_6315_:
{
return v___x_6316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_){
_start:
{
lean_object* v_res_6469_; 
v_res_6469_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6459_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_, v_a_6467_);
lean_dec(v_a_6467_);
lean_dec_ref(v_a_6466_);
lean_dec(v_a_6465_);
lean_dec_ref(v_a_6464_);
lean_dec(v_a_6463_);
lean_dec_ref(v_a_6462_);
lean_dec(v_a_6461_);
lean_dec_ref(v_a_6460_);
return v_res_6469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6470_, lean_object* v_msg_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_){
_start:
{
lean_object* v___x_6481_; 
v___x_6481_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6471_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_);
return v___x_6481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6482_, lean_object* v_msg_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_){
_start:
{
lean_object* v_res_6493_; 
v_res_6493_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6482_, v_msg_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6490_);
lean_dec(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec(v___y_6485_);
lean_dec_ref(v___y_6484_);
return v_res_6493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; 
v___x_6499_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6503_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6499_, v___x_6500_, v___x_6501_, v___x_6502_);
return v___x_6503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6504_){
_start:
{
lean_object* v_res_6505_; 
v_res_6505_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6506_, lean_object* v_ty_x3f_6507_, lean_object* v_a_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_){
_start:
{
lean_object* v___x_6518_; 
v___x_6518_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6506_, v_ty_x3f_6507_, v_a_6508_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_);
if (lean_obj_tag(v___x_6518_) == 0)
{
lean_object* v_a_6519_; lean_object* v___x_6520_; 
v_a_6519_ = lean_ctor_get(v___x_6518_, 0);
lean_inc(v_a_6519_);
lean_dec_ref_known(v___x_6518_, 1);
v___x_6520_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6519_, v___y_6510_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_);
return v___x_6520_;
}
else
{
lean_object* v_a_6521_; lean_object* v___x_6523_; uint8_t v_isShared_6524_; uint8_t v_isSharedCheck_6528_; 
v_a_6521_ = lean_ctor_get(v___x_6518_, 0);
v_isSharedCheck_6528_ = !lean_is_exclusive(v___x_6518_);
if (v_isSharedCheck_6528_ == 0)
{
v___x_6523_ = v___x_6518_;
v_isShared_6524_ = v_isSharedCheck_6528_;
goto v_resetjp_6522_;
}
else
{
lean_inc(v_a_6521_);
lean_dec(v___x_6518_);
v___x_6523_ = lean_box(0);
v_isShared_6524_ = v_isSharedCheck_6528_;
goto v_resetjp_6522_;
}
v_resetjp_6522_:
{
lean_object* v___x_6526_; 
if (v_isShared_6524_ == 0)
{
v___x_6526_ = v___x_6523_;
goto v_reusejp_6525_;
}
else
{
lean_object* v_reuseFailAlloc_6527_; 
v_reuseFailAlloc_6527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
v___x_6526_ = v_reuseFailAlloc_6527_;
goto v_reusejp_6525_;
}
v_reusejp_6525_:
{
return v___x_6526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6529_, lean_object* v_ty_x3f_6530_, lean_object* v_a_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6529_, v_ty_x3f_6530_, v_a_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
lean_dec(v___y_6537_);
lean_dec_ref(v___y_6536_);
lean_dec(v___y_6535_);
lean_dec_ref(v___y_6534_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6532_);
return v_res_6541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6548_, lean_object* v_a_6549_, lean_object* v_a_6550_, lean_object* v_a_6551_, lean_object* v_a_6552_, lean_object* v_a_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_, lean_object* v_a_6556_){
_start:
{
lean_object* v___x_6558_; uint8_t v___x_6559_; 
v___x_6558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6548_);
v___x_6559_ = l_Lean_Syntax_isOfKind(v_stx_6548_, v___x_6558_);
if (v___x_6559_ == 0)
{
lean_object* v___x_6560_; 
lean_dec(v_stx_6548_);
v___x_6560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6560_;
}
else
{
lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v_ty_x3f_6564_; lean_object* v___y_6565_; lean_object* v___y_6566_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; lean_object* v___x_6586_; lean_object* v___x_6587_; uint8_t v___x_6588_; 
v___x_6561_ = lean_unsigned_to_nat(1u);
v___x_6562_ = l_Lean_Syntax_getArg(v_stx_6548_, v___x_6561_);
v___x_6586_ = lean_unsigned_to_nat(2u);
v___x_6587_ = l_Lean_Syntax_getArg(v_stx_6548_, v___x_6586_);
lean_dec(v_stx_6548_);
v___x_6588_ = l_Lean_Syntax_isNone(v___x_6587_);
if (v___x_6588_ == 0)
{
uint8_t v___x_6589_; 
lean_inc(v___x_6587_);
v___x_6589_ = l_Lean_Syntax_matchesNull(v___x_6587_, v___x_6586_);
if (v___x_6589_ == 0)
{
lean_object* v___x_6590_; 
lean_dec(v___x_6587_);
lean_dec(v___x_6562_);
v___x_6590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6590_;
}
else
{
lean_object* v_ty_x3f_6591_; lean_object* v___x_6592_; 
v_ty_x3f_6591_ = l_Lean_Syntax_getArg(v___x_6587_, v___x_6561_);
lean_dec(v___x_6587_);
v___x_6592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6592_, 0, v_ty_x3f_6591_);
v_ty_x3f_6564_ = v___x_6592_;
v___y_6565_ = v_a_6549_;
v___y_6566_ = v_a_6550_;
v___y_6567_ = v_a_6551_;
v___y_6568_ = v_a_6552_;
v___y_6569_ = v_a_6553_;
v___y_6570_ = v_a_6554_;
v___y_6571_ = v_a_6555_;
v___y_6572_ = v_a_6556_;
goto v___jp_6563_;
}
}
else
{
lean_object* v___x_6593_; 
lean_dec(v___x_6587_);
v___x_6593_ = lean_box(0);
v_ty_x3f_6564_ = v___x_6593_;
v___y_6565_ = v_a_6549_;
v___y_6566_ = v_a_6550_;
v___y_6567_ = v_a_6551_;
v___y_6568_ = v_a_6552_;
v___y_6569_ = v_a_6553_;
v___y_6570_ = v_a_6554_;
v___y_6571_ = v_a_6555_;
v___y_6572_ = v_a_6556_;
goto v___jp_6563_;
}
v___jp_6563_:
{
lean_object* v___x_6573_; 
v___x_6573_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6566_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6573_) == 0)
{
lean_object* v_a_6574_; lean_object* v_pats_6575_; lean_object* v___f_6576_; lean_object* v___x_6577_; 
v_a_6574_ = lean_ctor_get(v___x_6573_, 0);
lean_inc_n(v_a_6574_, 2);
lean_dec_ref_known(v___x_6573_, 1);
v_pats_6575_ = l_Lean_Syntax_getArgs(v___x_6562_);
lean_dec(v___x_6562_);
v___f_6576_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6576_, 0, v_pats_6575_);
lean_closure_set(v___f_6576_, 1, v_ty_x3f_6564_);
lean_closure_set(v___f_6576_, 2, v_a_6574_);
v___x_6577_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6574_, v___f_6576_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
return v___x_6577_;
}
else
{
lean_object* v_a_6578_; lean_object* v___x_6580_; uint8_t v_isShared_6581_; uint8_t v_isSharedCheck_6585_; 
lean_dec(v_ty_x3f_6564_);
lean_dec(v___x_6562_);
v_a_6578_ = lean_ctor_get(v___x_6573_, 0);
v_isSharedCheck_6585_ = !lean_is_exclusive(v___x_6573_);
if (v_isSharedCheck_6585_ == 0)
{
v___x_6580_ = v___x_6573_;
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
else
{
lean_inc(v_a_6578_);
lean_dec(v___x_6573_);
v___x_6580_ = lean_box(0);
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
v_resetjp_6579_:
{
lean_object* v___x_6583_; 
if (v_isShared_6581_ == 0)
{
v___x_6583_ = v___x_6580_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_a_6578_);
v___x_6583_ = v_reuseFailAlloc_6584_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
return v___x_6583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6594_, lean_object* v_a_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6594_, v_a_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_, v_a_6602_);
lean_dec(v_a_6602_);
lean_dec_ref(v_a_6601_);
lean_dec(v_a_6600_);
lean_dec_ref(v_a_6599_);
lean_dec(v_a_6598_);
lean_dec_ref(v_a_6597_);
lean_dec(v_a_6596_);
lean_dec_ref(v_a_6595_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; 
v___x_6610_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6613_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6614_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6610_, v___x_6611_, v___x_6612_, v___x_6613_);
return v___x_6614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6615_){
_start:
{
lean_object* v_res_6616_; 
v_res_6616_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6616_;
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
