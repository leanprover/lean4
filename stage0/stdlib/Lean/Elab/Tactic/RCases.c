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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v___x_867_, 0, v___y_863_);
lean_ctor_set(v___x_867_, 1, v___y_862_);
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
v___y_862_ = v_snd_875_;
v___y_863_ = v___y_870_;
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
v___y_862_ = v_snd_875_;
v___y_863_ = v___y_870_;
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
lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v_mctx_1112_; lean_object* v_lctx_1113_; lean_object* v_options_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_st_ref_get(v___y_1105_);
v_mctx_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_mctx_1112_);
lean_dec(v___x_1111_);
v_lctx_1113_ = lean_ctor_get(v___y_1104_, 2);
v_options_1114_ = lean_ctor_get(v___y_1106_, 2);
lean_inc_ref(v_options_1114_);
lean_inc_ref(v_lctx_1113_);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v_env_1110_);
lean_ctor_set(v___x_1115_, 1, v_mctx_1112_);
lean_ctor_set(v___x_1115_, 2, v_lctx_1113_);
lean_ctor_set(v___x_1115_, 3, v_options_1114_);
v___x_1116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_msgData_1103_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msgData_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_ref_1131_ = lean_ctor_get(v___y_1128_, 5);
v___x_1132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_inc(v_ref_1131_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_ref_1131_);
lean_ctor_set(v___x_1137_, 1, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_fileName_1156_; lean_object* v_fileMap_1157_; lean_object* v_options_1158_; lean_object* v_currRecDepth_1159_; lean_object* v_maxRecDepth_1160_; lean_object* v_ref_1161_; lean_object* v_currNamespace_1162_; lean_object* v_openDecls_1163_; lean_object* v_initHeartbeats_1164_; lean_object* v_maxHeartbeats_1165_; lean_object* v_quotContext_1166_; lean_object* v_currMacroScope_1167_; uint8_t v_diag_1168_; lean_object* v_cancelTk_x3f_1169_; uint8_t v_suppressElabErrors_1170_; lean_object* v_inheritedTraceOptions_1171_; lean_object* v_ref_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_fileName_1156_ = lean_ctor_get(v___y_1153_, 0);
v_fileMap_1157_ = lean_ctor_get(v___y_1153_, 1);
v_options_1158_ = lean_ctor_get(v___y_1153_, 2);
v_currRecDepth_1159_ = lean_ctor_get(v___y_1153_, 3);
v_maxRecDepth_1160_ = lean_ctor_get(v___y_1153_, 4);
v_ref_1161_ = lean_ctor_get(v___y_1153_, 5);
v_currNamespace_1162_ = lean_ctor_get(v___y_1153_, 6);
v_openDecls_1163_ = lean_ctor_get(v___y_1153_, 7);
v_initHeartbeats_1164_ = lean_ctor_get(v___y_1153_, 8);
v_maxHeartbeats_1165_ = lean_ctor_get(v___y_1153_, 9);
v_quotContext_1166_ = lean_ctor_get(v___y_1153_, 10);
v_currMacroScope_1167_ = lean_ctor_get(v___y_1153_, 11);
v_diag_1168_ = lean_ctor_get_uint8(v___y_1153_, sizeof(void*)*14);
v_cancelTk_x3f_1169_ = lean_ctor_get(v___y_1153_, 12);
v_suppressElabErrors_1170_ = lean_ctor_get_uint8(v___y_1153_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1171_ = lean_ctor_get(v___y_1153_, 13);
v_ref_1172_ = l_Lean_replaceRef(v_ref_1149_, v_ref_1161_);
lean_inc_ref(v_inheritedTraceOptions_1171_);
lean_inc(v_cancelTk_x3f_1169_);
lean_inc(v_currMacroScope_1167_);
lean_inc(v_quotContext_1166_);
lean_inc(v_maxHeartbeats_1165_);
lean_inc(v_initHeartbeats_1164_);
lean_inc(v_openDecls_1163_);
lean_inc(v_currNamespace_1162_);
lean_inc(v_maxRecDepth_1160_);
lean_inc(v_currRecDepth_1159_);
lean_inc_ref(v_options_1158_);
lean_inc_ref(v_fileMap_1157_);
lean_inc_ref(v_fileName_1156_);
v___x_1173_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1173_, 0, v_fileName_1156_);
lean_ctor_set(v___x_1173_, 1, v_fileMap_1157_);
lean_ctor_set(v___x_1173_, 2, v_options_1158_);
lean_ctor_set(v___x_1173_, 3, v_currRecDepth_1159_);
lean_ctor_set(v___x_1173_, 4, v_maxRecDepth_1160_);
lean_ctor_set(v___x_1173_, 5, v_ref_1172_);
lean_ctor_set(v___x_1173_, 6, v_currNamespace_1162_);
lean_ctor_set(v___x_1173_, 7, v_openDecls_1163_);
lean_ctor_set(v___x_1173_, 8, v_initHeartbeats_1164_);
lean_ctor_set(v___x_1173_, 9, v_maxHeartbeats_1165_);
lean_ctor_set(v___x_1173_, 10, v_quotContext_1166_);
lean_ctor_set(v___x_1173_, 11, v_currMacroScope_1167_);
lean_ctor_set(v___x_1173_, 12, v_cancelTk_x3f_1169_);
lean_ctor_set(v___x_1173_, 13, v_inheritedTraceOptions_1171_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*14, v_diag_1168_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*14 + 1, v_suppressElabErrors_1170_);
v___x_1174_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1150_, v___y_1151_, v___y_1152_, v___x_1173_, v___y_1154_);
lean_dec_ref_known(v___x_1173_, 14);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1175_, lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1175_, v_msg_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v_ref_1175_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1183_, lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_a_1192_; lean_object* v___x_1193_; 
v___x_1191_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_msg_1184_, v_declHint_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1183_, v_a_1192_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1194_, lean_object* v_msg_1195_, lean_object* v_declHint_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1194_, v_msg_1195_, v_declHint_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v_ref_1194_);
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1209_, lean_object* v_constName_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1216_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1217_ = 0;
lean_inc(v_constName_1210_);
v___x_1218_ = l_Lean_MessageData_ofConstName(v_constName_1210_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1216_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1209_, v___x_1221_, v_constName_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1223_, lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1223_, v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_ref_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_ref_1237_; lean_object* v___x_1238_; 
v_ref_1237_ = lean_ctor_get(v___y_1234_, 5);
v___x_1238_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1237_, v_constName_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(lean_object* v_constName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_env_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_st_ref_get(v___y_1250_);
v_env_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc_ref(v_env_1253_);
lean_dec(v___x_1252_);
v___x_1254_ = 0;
lean_inc(v_constName_1246_);
v___x_1255_ = l_Lean_Environment_findConstVal_x3f(v_env_1253_, v_constName_1246_, v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1256_;
}
else
{
lean_object* v_val_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_constName_1246_);
v_val_1257_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1255_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_val_1257_);
lean_dec(v___x_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 0);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_val_1257_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0___boxed(lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
if (lean_obj_tag(v_a_1272_) == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = l_List_reverse___redArg(v_a_1273_);
return v___x_1274_;
}
else
{
lean_object* v_head_1275_; lean_object* v_tail_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_head_1275_ = lean_ctor_get(v_a_1272_, 0);
v_tail_1276_ = lean_ctor_get(v_a_1272_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1272_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v_a_1272_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_tail_1276_);
lean_inc(v_head_1275_);
lean_dec(v_a_1272_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = l_Lean_mkLevelParam(v_head_1275_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v_a_1273_);
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1273_);
v___x_1282_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_a_1272_ = v_tail_1276_;
v_a_1273_ = v___x_1282_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
lean_inc(v_constName_1286_);
v___x_1292_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0(v_constName_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1304_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1304_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1304_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_levelParams_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_levelParams_1297_ = lean_ctor_get(v_a_1293_, 1);
lean_inc(v_levelParams_1297_);
lean_dec(v_a_1293_);
v___x_1298_ = lean_box(0);
v___x_1299_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__1(v_levelParams_1297_, v___x_1298_);
v___x_1300_ = l_Lean_mkConst(v_constName_1286_, v___x_1299_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1300_);
v___x_1302_ = v___x_1295_;
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
lean_dec(v_constName_1286_);
v_a_1305_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1292_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1292_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0___boxed(lean_object* v_constName_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_constName_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(lean_object* v_ref_1320_, lean_object* v_params_1321_, lean_object* v_altVarNames_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v_x_1324_);
lean_dec(v_ref_1320_);
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_altVarNames_1322_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v_head_1333_; lean_object* v_tail_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1440_; 
v_head_1333_ = lean_ctor_get(v_x_1323_, 0);
v_tail_1334_ = lean_ctor_get(v_x_1323_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1336_ = v_x_1323_;
v_isShared_1337_ = v_isSharedCheck_1440_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_tail_1334_);
lean_inc(v_head_1333_);
lean_dec(v_x_1323_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1440_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; 
lean_inc(v_head_1333_);
v___x_1338_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0(v_head_1333_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = lean_box(0);
v___x_1341_ = l_Lean_Meta_getFunInfo(v_a_1339_, v___x_1340_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v_paramInfo_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1422_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v_paramInfo_1343_ = lean_ctor_get(v_a_1342_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_a_1342_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v_a_1342_, 1);
lean_dec(v_unused_1423_);
v___x_1345_ = v_a_1342_;
v_isShared_1346_ = v_isSharedCheck_1422_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_paramInfo_1343_);
lean_dec(v_a_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1422_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1387_; uint8_t v_fst_1388_; lean_object* v_snd_1389_; lean_object* v_snd_1390_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1417_; 
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_1417_ = v___x_1420_;
goto v___jp_1416_;
}
else
{
lean_object* v_head_1421_; 
v_head_1421_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_head_1421_);
v___y_1417_ = v_head_1421_;
goto v___jp_1416_;
}
v___jp_1347_:
{
lean_object* v___x_1352_; lean_object* v_fst_1353_; lean_object* v_snd_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1385_; 
v___x_1352_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1351_, v_paramInfo_1343_, v___y_1349_, v_params_1321_, v___y_1348_);
lean_dec_ref(v_paramInfo_1343_);
v_fst_1353_ = lean_ctor_get(v___x_1352_, 0);
v_snd_1354_ = lean_ctor_get(v___x_1352_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1356_ = v___x_1352_;
v_isShared_1357_ = v_isSharedCheck_1385_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_snd_1354_);
lean_inc(v_fst_1353_);
lean_dec(v___x_1352_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1385_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = 1;
v___x_1359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1359_, 0, v_fst_1353_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*1, v___x_1358_);
v___x_1360_ = lean_array_push(v_altVarNames_1322_, v___x_1359_);
v___x_1361_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1320_, v_params_1321_, v___x_1360_, v_tail_1334_, v___y_1350_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1384_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1384_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1384_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1383_; 
v_fst_1366_ = lean_ctor_get(v_a_1362_, 0);
v_snd_1367_ = lean_ctor_get(v_a_1362_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1369_ = v_a_1362_;
v_isShared_1370_ = v_isSharedCheck_1383_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_a_1362_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1383_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_snd_1354_);
lean_ctor_set(v___x_1369_, 0, v_head_1333_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_head_1333_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_snd_1354_);
v___x_1372_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_snd_1367_);
lean_ctor_set(v___x_1336_, 0, v___x_1372_);
v___x_1374_ = v___x_1336_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1367_);
v___x_1374_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1374_);
lean_ctor_set(v___x_1356_, 0, v_fst_1366_);
v___x_1376_ = v___x_1356_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_fst_1366_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1376_);
v___x_1378_ = v___x_1364_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1356_);
lean_dec(v_snd_1354_);
lean_del_object(v___x_1336_);
lean_dec(v_head_1333_);
return v___x_1361_;
}
}
}
v___jp_1386_:
{
lean_object* v_ref_1391_; 
v_ref_1391_ = lean_ctor_get(v___y_1387_, 0);
lean_inc(v_ref_1391_);
lean_dec_ref(v___y_1387_);
v___y_1348_ = v_snd_1389_;
v___y_1349_ = v_fst_1388_;
v___y_1350_ = v_snd_1390_;
v___y_1351_ = v_ref_1391_;
goto v___jp_1347_;
}
v___jp_1392_:
{
lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; uint8_t v___x_1398_; 
lean_inc_ref(v___y_1394_);
v___x_1395_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1394_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_unbox(v_fst_1396_);
lean_dec(v_fst_1396_);
v___y_1387_ = v___y_1394_;
v_fst_1388_ = v___x_1398_;
v_snd_1389_ = v_snd_1397_;
v_snd_1390_ = v___y_1393_;
goto v___jp_1386_;
}
v___jp_1399_:
{
if (lean_obj_tag(v_tail_1334_) == 0)
{
if (lean_obj_tag(v___y_1402_) == 1)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v___y_1402_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1414_ = lean_ctor_get(v___y_1402_, 1);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v___y_1402_, 0);
lean_dec(v_unused_1415_);
v___x_1404_ = v___y_1402_;
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v___y_1402_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = 0;
lean_inc(v_ref_1320_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 6);
lean_ctor_set(v___x_1345_, 1, v_x_1324_);
lean_ctor_set(v___x_1345_, 0, v_ref_1320_);
v___x_1408_ = v___x_1345_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_ref_1320_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_x_1324_);
v___x_1408_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
lean_inc(v___y_1401_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___y_1401_);
lean_ctor_set(v___x_1404_, 0, v___x_1408_);
v___x_1410_ = v___x_1404_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___y_1401_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v___y_1387_ = v___y_1400_;
v_fst_1388_ = v___x_1406_;
v_snd_1389_ = v___x_1410_;
v_snd_1390_ = v___y_1401_;
goto v___jp_1386_;
}
}
}
}
else
{
lean_dec(v___y_1401_);
lean_del_object(v___x_1345_);
lean_dec(v_x_1324_);
v___y_1393_ = v___y_1402_;
v___y_1394_ = v___y_1400_;
goto v___jp_1392_;
}
}
else
{
lean_dec(v___y_1401_);
lean_del_object(v___x_1345_);
lean_dec(v_x_1324_);
v___y_1393_ = v___y_1402_;
v___y_1394_ = v___y_1400_;
goto v___jp_1392_;
}
}
v___jp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_box(0);
if (lean_obj_tag(v_x_1324_) == 0)
{
v___y_1400_ = v___y_1417_;
v___y_1401_ = v___x_1418_;
v___y_1402_ = v___x_1418_;
goto v___jp_1399_;
}
else
{
lean_object* v_tail_1419_; 
v_tail_1419_ = lean_ctor_get(v_x_1324_, 1);
lean_inc(v_tail_1419_);
v___y_1400_ = v___y_1417_;
v___y_1401_ = v___x_1418_;
v___y_1402_ = v_tail_1419_;
goto v___jp_1399_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_del_object(v___x_1336_);
lean_dec(v_tail_1334_);
lean_dec(v_head_1333_);
lean_dec(v_x_1324_);
lean_dec_ref(v_altVarNames_1322_);
lean_dec(v_ref_1320_);
v_a_1424_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1341_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1341_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1336_);
lean_dec(v_tail_1334_);
lean_dec(v_head_1333_);
lean_dec(v_x_1324_);
lean_dec_ref(v_altVarNames_1322_);
lean_dec(v_ref_1320_);
v_a_1432_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1338_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1338_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors___boxed(lean_object* v_ref_1441_, lean_object* v_params_1442_, lean_object* v_altVarNames_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1441_, v_params_1442_, v_altVarNames_1443_, v_x_1444_, v_x_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_params_1442_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1452_, lean_object* v_constName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___redArg(v_constName_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1(v_00_u03b1_1460_, v_constName_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1468_, lean_object* v_ref_1469_, lean_object* v_constName_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1469_, v_constName_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1477_, lean_object* v_ref_1478_, lean_object* v_constName_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1477_, v_ref_1478_, v_constName_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_ref_1478_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1486_, lean_object* v_ref_1487_, lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1487_, v_msg_1488_, v_declHint_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_ref_1497_, lean_object* v_msg_1498_, lean_object* v_declHint_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1496_, v_ref_1497_, v_msg_1498_, v_declHint_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v_ref_1497_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_msg_1506_, lean_object* v_declHint_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_msg_1506_, v_declHint_1507_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5_spec__6(v_msg_1514_, v_declHint_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_ref_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_ref_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1531_, v_ref_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v_ref_1532_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msg_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1548_, v_msg_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(lean_object* v_e_1556_, lean_object* v_cont_1557_, lean_object* v_g_1558_, lean_object* v_fs_1559_, lean_object* v_clears_1560_, lean_object* v_a_1561_, lean_object* v_ref_1562_, lean_object* v_a_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_Expr_isFVar(v_e_1556_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_ref_1562_);
lean_dec_ref(v_e_1556_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
v___x_1572_ = lean_apply_11(v_cont_1557_, v_g_1558_, v_fs_1559_, v_clears_1560_, v_a_1561_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, lean_box(0));
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_1562_, v_e_1556_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1573_, 1);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
v___x_1574_ = lean_apply_11(v_cont_1557_, v_g_1558_, v_fs_1559_, v_clears_1560_, v_a_1561_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, lean_box(0));
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1561_);
lean_dec_ref(v_clears_1560_);
lean_dec(v_fs_1559_);
lean_dec(v_g_1558_);
lean_dec_ref(v_cont_1557_);
v_a_1575_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1573_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1573_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed(lean_object* v_e_1583_, lean_object* v_cont_1584_, lean_object* v_g_1585_, lean_object* v_fs_1586_, lean_object* v_clears_1587_, lean_object* v_a_1588_, lean_object* v_ref_1589_, lean_object* v_a_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1(v_e_1583_, v_cont_1584_, v_g_1585_, v_fs_1586_, v_clears_1587_, v_a_1588_, v_ref_1589_, v_a_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v_a_1590_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(lean_object* v_x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
v___x_1607_ = lean_apply_7(v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed(lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0(v_x_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(lean_object* v_mvarId_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___f_1626_; lean_object* v___x_1627_; 
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1626_, 0, v_x_1618_);
lean_closure_set(v___f_1626_, 1, v___y_1619_);
lean_closure_set(v___f_1626_, 2, v___y_1620_);
v___x_1627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1617_, v___f_1626_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
return v___x_1627_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg___boxed(lean_object* v_mvarId_1636_, lean_object* v_x_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_1636_, v_x_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__0));
v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__2));
v___x_1651_ = l_Lean_stringToMessageData(v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 1)
{
lean_object* v_fvarId_1658_; lean_object* v___x_1659_; 
v_fvarId_1658_ = lean_ctor_get(v_x_1652_, 0);
lean_inc(v_fvarId_1658_);
lean_dec_ref_known(v_x_1652_, 1);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_fvarId_1658_);
return v___x_1659_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_1661_ = l_Lean_MessageData_ofExpr(v_x_1652_);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__3);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v___x_1664_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___boxed(lean_object* v_x_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0(v_x_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_ks_1677_; lean_object* v_vs_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1702_; 
v_ks_1677_ = lean_ctor_get(v_x_1673_, 0);
v_vs_1678_ = lean_ctor_get(v_x_1673_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1673_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1680_ = v_x_1673_;
v_isShared_1681_ = v_isSharedCheck_1702_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_vs_1678_);
lean_inc(v_ks_1677_);
lean_dec(v_x_1673_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1702_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = lean_array_get_size(v_ks_1677_);
v___x_1683_ = lean_nat_dec_lt(v_x_1674_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec(v_x_1674_);
v___x_1684_ = lean_array_push(v_ks_1677_, v_x_1675_);
v___x_1685_ = lean_array_push(v_vs_1678_, v_x_1676_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1685_);
lean_ctor_set(v___x_1680_, 0, v___x_1684_);
v___x_1687_ = v___x_1680_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v_k_x27_1689_; uint8_t v___x_1690_; 
v_k_x27_1689_ = lean_array_fget_borrowed(v_ks_1677_, v_x_1674_);
v___x_1690_ = l_Lean_instBEqMVarId_beq(v_x_1675_, v_k_x27_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1692_; 
if (v_isShared_1681_ == 0)
{
v___x_1692_ = v___x_1680_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_ks_1677_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_vs_1678_);
v___x_1692_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_add(v_x_1674_, v___x_1693_);
lean_dec(v_x_1674_);
v_x_1673_ = v___x_1692_;
v_x_1674_ = v___x_1694_;
goto _start;
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = lean_array_fset(v_ks_1677_, v_x_1674_, v_x_1675_);
v___x_1698_ = lean_array_fset(v_vs_1678_, v_x_1674_, v_x_1676_);
lean_dec(v_x_1674_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1698_);
lean_ctor_set(v___x_1680_, 0, v___x_1697_);
v___x_1700_ = v___x_1680_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(lean_object* v_n_1703_, lean_object* v_k_1704_, lean_object* v_v_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_n_1703_, v___x_1706_, v_k_1704_, v_v_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(lean_object* v_x_1709_, size_t v_x_1710_, size_t v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v_es_1714_; size_t v___x_1715_; size_t v___x_1716_; lean_object* v_j_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_es_1714_ = lean_ctor_get(v_x_1709_, 0);
v___x_1715_ = ((size_t)31ULL);
v___x_1716_ = lean_usize_land(v_x_1710_, v___x_1715_);
v_j_1717_ = lean_usize_to_nat(v___x_1716_);
v___x_1718_ = lean_array_get_size(v_es_1714_);
v___x_1719_ = lean_nat_dec_lt(v_j_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec(v_j_1717_);
lean_dec(v_x_1713_);
lean_dec(v_x_1712_);
return v_x_1709_;
}
else
{
lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1758_; 
lean_inc_ref(v_es_1714_);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_x_1709_, 0);
lean_dec(v_unused_1759_);
v___x_1721_ = v_x_1709_;
v_isShared_1722_ = v_isSharedCheck_1758_;
goto v_resetjp_1720_;
}
else
{
lean_dec(v_x_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1758_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_v_1723_; lean_object* v___x_1724_; lean_object* v_xs_x27_1725_; lean_object* v___y_1727_; 
v_v_1723_ = lean_array_fget(v_es_1714_, v_j_1717_);
v___x_1724_ = lean_box(0);
v_xs_x27_1725_ = lean_array_fset(v_es_1714_, v_j_1717_, v___x_1724_);
switch(lean_obj_tag(v_v_1723_))
{
case 0:
{
lean_object* v_key_1732_; lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1743_; 
v_key_1732_ = lean_ctor_get(v_v_1723_, 0);
v_val_1733_ = lean_ctor_get(v_v_1723_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_v_1723_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1735_ = v_v_1723_;
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_inc(v_key_1732_);
lean_dec(v_v_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
uint8_t v___x_1737_; 
v___x_1737_ = l_Lean_instBEqMVarId_beq(v_x_1712_, v_key_1732_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_del_object(v___x_1735_);
v___x_1738_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1732_, v_val_1733_, v_x_1712_, v_x_1713_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___y_1727_ = v___x_1739_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1741_; 
lean_dec(v_val_1733_);
lean_dec(v_key_1732_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v_x_1713_);
lean_ctor_set(v___x_1735_, 0, v_x_1712_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_x_1712_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_x_1713_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
v___y_1727_ = v___x_1741_;
goto v___jp_1726_;
}
}
}
}
case 1:
{
lean_object* v_node_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1756_; 
v_node_1744_ = lean_ctor_get(v_v_1723_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_v_1723_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1746_ = v_v_1723_;
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_node_1744_);
lean_dec(v_v_1723_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1756_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
size_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1748_ = ((size_t)5ULL);
v___x_1749_ = lean_usize_shift_right(v_x_1710_, v___x_1748_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_x_1711_, v___x_1750_);
v___x_1752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_node_1744_, v___x_1749_, v___x_1751_, v_x_1712_, v_x_1713_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1752_);
v___x_1754_ = v___x_1746_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
v___y_1727_ = v___x_1754_;
goto v___jp_1726_;
}
}
}
default: 
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_x_1712_);
lean_ctor_set(v___x_1757_, 1, v_x_1713_);
v___y_1727_ = v___x_1757_;
goto v___jp_1726_;
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_array_fset(v_xs_x27_1725_, v_j_1717_, v___y_1727_);
lean_dec(v_j_1717_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1728_);
v___x_1730_ = v___x_1721_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1781_; 
v_ks_1760_ = lean_ctor_get(v_x_1709_, 0);
v_vs_1761_ = lean_ctor_get(v_x_1709_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1763_ = v_x_1709_;
v_isShared_1764_ = v_isSharedCheck_1781_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_vs_1761_);
lean_inc(v_ks_1760_);
lean_dec(v_x_1709_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1781_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_ks_1760_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_vs_1761_);
v___x_1766_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_newNode_1767_; uint8_t v___y_1769_; size_t v___x_1775_; uint8_t v___x_1776_; 
v_newNode_1767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1766_, v_x_1712_, v_x_1713_);
v___x_1775_ = ((size_t)7ULL);
v___x_1776_ = lean_usize_dec_le(v___x_1775_, v_x_1711_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1767_);
v___x_1778_ = lean_unsigned_to_nat(4u);
v___x_1779_ = lean_nat_dec_lt(v___x_1777_, v___x_1778_);
lean_dec(v___x_1777_);
v___y_1769_ = v___x_1779_;
goto v___jp_1768_;
}
else
{
v___y_1769_ = v___x_1776_;
goto v___jp_1768_;
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
lean_object* v_ks_1770_; lean_object* v_vs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_ks_1770_ = lean_ctor_get(v_newNode_1767_, 0);
lean_inc_ref(v_ks_1770_);
v_vs_1771_ = lean_ctor_get(v_newNode_1767_, 1);
lean_inc_ref(v_vs_1771_);
lean_dec_ref(v_newNode_1767_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1711_, v_ks_1770_, v_vs_1771_, v___x_1772_, v___x_1773_);
lean_dec_ref(v_vs_1771_);
lean_dec_ref(v_ks_1770_);
return v___x_1774_;
}
else
{
return v_newNode_1767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1782_, lean_object* v_keys_1783_, lean_object* v_vals_1784_, lean_object* v_i_1785_, lean_object* v_entries_1786_){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_array_get_size(v_keys_1783_);
v___x_1788_ = lean_nat_dec_lt(v_i_1785_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec(v_i_1785_);
return v_entries_1786_;
}
else
{
lean_object* v_k_1789_; lean_object* v_v_1790_; uint64_t v___x_1791_; size_t v_h_1792_; size_t v___x_1793_; lean_object* v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v_h_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_k_1789_ = lean_array_fget_borrowed(v_keys_1783_, v_i_1785_);
v_v_1790_ = lean_array_fget_borrowed(v_vals_1784_, v_i_1785_);
v___x_1791_ = l_Lean_instHashableMVarId_hash(v_k_1789_);
v_h_1792_ = lean_uint64_to_usize(v___x_1791_);
v___x_1793_ = ((size_t)5ULL);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_sub(v_depth_1782_, v___x_1795_);
v___x_1797_ = lean_usize_mul(v___x_1793_, v___x_1796_);
v_h_1798_ = lean_usize_shift_right(v_h_1792_, v___x_1797_);
v___x_1799_ = lean_nat_add(v_i_1785_, v___x_1794_);
lean_dec(v_i_1785_);
lean_inc(v_v_1790_);
lean_inc(v_k_1789_);
v___x_1800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1786_, v_h_1798_, v_depth_1782_, v_k_1789_, v_v_1790_);
v_i_1785_ = v___x_1799_;
v_entries_1786_ = v___x_1800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1802_, lean_object* v_keys_1803_, lean_object* v_vals_1804_, lean_object* v_i_1805_, lean_object* v_entries_1806_){
_start:
{
size_t v_depth_boxed_1807_; lean_object* v_res_1808_; 
v_depth_boxed_1807_ = lean_unbox_usize(v_depth_1802_);
lean_dec(v_depth_1802_);
v_res_1808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1807_, v_keys_1803_, v_vals_1804_, v_i_1805_, v_entries_1806_);
lean_dec_ref(v_vals_1804_);
lean_dec_ref(v_keys_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
size_t v_x_19086__boxed_1814_; size_t v_x_19087__boxed_1815_; lean_object* v_res_1816_; 
v_x_19086__boxed_1814_ = lean_unbox_usize(v_x_1810_);
lean_dec(v_x_1810_);
v_x_19087__boxed_1815_ = lean_unbox_usize(v_x_1811_);
lean_dec(v_x_1811_);
v_res_1816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1809_, v_x_19086__boxed_1814_, v_x_19087__boxed_1815_, v_x_1812_, v_x_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint64_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = l_Lean_instHashableMVarId_hash(v_x_1818_);
v___x_1821_ = lean_uint64_to_usize(v___x_1820_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1817_, v___x_1821_, v___x_1822_, v_x_1818_, v_x_1819_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1824_, lean_object* v_val_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v_mctx_1829_; lean_object* v_cache_1830_; lean_object* v_zetaDeltaFVarIds_1831_; lean_object* v_postponed_1832_; lean_object* v_diag_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1862_; 
v___x_1828_ = lean_st_ref_take(v___y_1826_);
v_mctx_1829_ = lean_ctor_get(v___x_1828_, 0);
v_cache_1830_ = lean_ctor_get(v___x_1828_, 1);
v_zetaDeltaFVarIds_1831_ = lean_ctor_get(v___x_1828_, 2);
v_postponed_1832_ = lean_ctor_get(v___x_1828_, 3);
v_diag_1833_ = lean_ctor_get(v___x_1828_, 4);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1835_ = v___x_1828_;
v_isShared_1836_ = v_isSharedCheck_1862_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_diag_1833_);
lean_inc(v_postponed_1832_);
lean_inc(v_zetaDeltaFVarIds_1831_);
lean_inc(v_cache_1830_);
lean_inc(v_mctx_1829_);
lean_dec(v___x_1828_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1862_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_depth_1837_; lean_object* v_levelAssignDepth_1838_; lean_object* v_lmvarCounter_1839_; lean_object* v_mvarCounter_1840_; lean_object* v_lDecls_1841_; lean_object* v_decls_1842_; lean_object* v_userNames_1843_; lean_object* v_lAssignment_1844_; lean_object* v_eAssignment_1845_; lean_object* v_dAssignment_1846_; lean_object* v_instanceTypedMVars_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1861_; 
v_depth_1837_ = lean_ctor_get(v_mctx_1829_, 0);
v_levelAssignDepth_1838_ = lean_ctor_get(v_mctx_1829_, 1);
v_lmvarCounter_1839_ = lean_ctor_get(v_mctx_1829_, 2);
v_mvarCounter_1840_ = lean_ctor_get(v_mctx_1829_, 3);
v_lDecls_1841_ = lean_ctor_get(v_mctx_1829_, 4);
v_decls_1842_ = lean_ctor_get(v_mctx_1829_, 5);
v_userNames_1843_ = lean_ctor_get(v_mctx_1829_, 6);
v_lAssignment_1844_ = lean_ctor_get(v_mctx_1829_, 7);
v_eAssignment_1845_ = lean_ctor_get(v_mctx_1829_, 8);
v_dAssignment_1846_ = lean_ctor_get(v_mctx_1829_, 9);
v_instanceTypedMVars_1847_ = lean_ctor_get(v_mctx_1829_, 10);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_mctx_1829_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1849_ = v_mctx_1829_;
v_isShared_1850_ = v_isSharedCheck_1861_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_instanceTypedMVars_1847_);
lean_inc(v_dAssignment_1846_);
lean_inc(v_eAssignment_1845_);
lean_inc(v_lAssignment_1844_);
lean_inc(v_userNames_1843_);
lean_inc(v_decls_1842_);
lean_inc(v_lDecls_1841_);
lean_inc(v_mvarCounter_1840_);
lean_inc(v_lmvarCounter_1839_);
lean_inc(v_levelAssignDepth_1838_);
lean_inc(v_depth_1837_);
lean_dec(v_mctx_1829_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1861_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1845_, v_mvarId_1824_, v_val_1825_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 8, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_depth_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_levelAssignDepth_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_lmvarCounter_1839_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_mvarCounter_1840_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_lDecls_1841_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_decls_1842_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_userNames_1843_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_lAssignment_1844_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1860_, 9, v_dAssignment_1846_);
lean_ctor_set(v_reuseFailAlloc_1860_, 10, v_instanceTypedMVars_1847_);
v___x_1853_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1853_);
v___x_1855_ = v___x_1835_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_cache_1830_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_zetaDeltaFVarIds_1831_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_postponed_1832_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_diag_1833_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_st_ref_put(v___y_1826_, v___x_1855_);
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_1863_, lean_object* v_val_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_1863_, v_val_1864_, v___y_1865_);
lean_dec(v___y_1865_);
return v_res_1867_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_15579__overap_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_15579__overap_1878_ = lean_panic_fn_borrowed(v___x_1877_, v_msg_1869_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1874_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1870_);
v___x_1879_ = lean_apply_7(v___x_15579__overap_1878_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, lean_box(0));
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_1889_, size_t v_i_1890_, size_t v_stop_1891_, lean_object* v_b_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_eq(v_i_1890_, v_stop_1891_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; 
v___x_1894_ = lean_array_uget_borrowed(v_as_1889_, v_i_1890_);
v_fst_1895_ = lean_ctor_get(v___x_1894_, 0);
v_snd_1896_ = lean_ctor_get(v___x_1894_, 1);
lean_inc(v_snd_1896_);
v___x_1897_ = l_Lean_mkFVar(v_snd_1896_);
lean_inc(v_fst_1895_);
v___x_1898_ = l_Lean_Meta_FVarSubst_insert(v_b_1892_, v_fst_1895_, v___x_1897_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_add(v_i_1890_, v___x_1899_);
v_i_1890_ = v___x_1900_;
v_b_1892_ = v___x_1898_;
goto _start;
}
else
{
return v_b_1892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_1902_, lean_object* v_i_1903_, lean_object* v_stop_1904_, lean_object* v_b_1905_){
_start:
{
size_t v_i_boxed_1906_; size_t v_stop_boxed_1907_; lean_object* v_res_1908_; 
v_i_boxed_1906_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_stop_boxed_1907_ = lean_unbox_usize(v_stop_1904_);
lean_dec(v_stop_1904_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_1902_, v_i_boxed_1906_, v_stop_boxed_1907_, v_b_1905_);
lean_dec_ref(v_as_1902_);
return v_res_1908_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1909_; lean_object* v_dummy_1910_; 
v___x_1909_ = lean_box(0);
v_dummy_1910_ = l_Lean_Expr_sort___override(v___x_1909_);
return v_dummy_1910_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_1915_ = lean_unsigned_to_nat(62u);
v___x_1916_ = lean_unsigned_to_nat(323u);
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_1918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_1919_ = l_mkPanicMessageWithDecl(v___x_1918_, v___x_1917_, v___x_1916_, v___x_1915_, v___x_1914_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(lean_object* v___x_1920_, lean_object* v___x_1921_, lean_object* v_snd_1922_, lean_object* v___x_1923_, lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v_e_1926_, lean_object* v___x_1927_, lean_object* v_head_1928_, lean_object* v_fst_1929_, lean_object* v_tail_1930_, uint8_t v___x_1931_, lean_object* v_snd_1932_, lean_object* v___x_1933_, lean_object* v_fs_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_getElimInfo(v___x_1920_, v___x_1921_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
lean_inc(v_snd_1922_);
v___x_1944_ = l_Lean_MVarId_getTag(v_snd_1922_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
lean_inc(v_a_1943_);
v___x_1946_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_1943_, v___x_1923_, v_a_1945_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_elimApp_1948_; lean_object* v_alts_1949_; lean_object* v_motivePos_1950_; lean_object* v_nargs_1951_; lean_object* v_dummy_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_elimApp_1948_ = lean_ctor_get(v_a_1947_, 0);
lean_inc_ref_n(v_elimApp_1948_, 2);
v_alts_1949_ = lean_ctor_get(v_a_1947_, 3);
lean_inc_ref(v_alts_1949_);
lean_dec(v_a_1947_);
v_motivePos_1950_ = lean_ctor_get(v_a_1943_, 2);
lean_inc(v_motivePos_1950_);
lean_dec(v_a_1943_);
v_nargs_1951_ = l_Lean_Expr_getAppNumArgs(v_elimApp_1948_);
v_dummy_1952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
lean_inc(v_nargs_1951_);
v___x_1953_ = lean_mk_array(v_nargs_1951_, v_dummy_1952_);
v___x_1954_ = lean_nat_sub(v_nargs_1951_, v___x_1924_);
lean_dec(v_nargs_1951_);
v___x_1955_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_1948_, v___x_1953_, v___x_1954_);
v___x_1956_ = lean_array_get(v___x_1925_, v___x_1955_, v_motivePos_1950_);
lean_dec(v_motivePos_1950_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = l_Lean_Expr_mvarId_x21(v___x_1956_);
lean_dec(v___x_1956_);
v___x_1958_ = l_Lean_Expr_fvarId_x21(v_e_1926_);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1924_);
lean_inc_ref(v___x_1959_);
v___x_1960_ = lean_array_push(v___x_1959_, v___x_1958_);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1927_);
lean_inc(v_snd_1922_);
v___x_1962_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_1922_, v___x_1957_, v___x_1960_, v___x_1961_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref_known(v___x_1962_, 1);
v___x_1963_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_1922_, v_elimApp_1948_, v___y_1938_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
lean_dec_ref_known(v___x_1963_, 1);
v___x_1964_ = lean_array_get_size(v_alts_1949_);
v___x_1965_ = lean_nat_dec_eq(v___x_1964_, v___x_1924_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_alts_1949_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
v___x_1966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4);
v___x_1967_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_1966_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; lean_object* v_name_1969_; lean_object* v_mvarId_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2042_; 
v___x_1968_ = lean_array_fget(v_alts_1949_, v___x_1927_);
lean_dec_ref(v_alts_1949_);
v_name_1969_ = lean_ctor_get(v___x_1968_, 0);
v_mvarId_1970_ = lean_ctor_get(v___x_1968_, 2);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_1968_, 1);
lean_dec(v_unused_2043_);
v___x_1972_ = v___x_1968_;
v_isShared_1973_ = v_isSharedCheck_2042_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_mvarId_1970_);
lean_inc(v_name_1969_);
lean_dec(v___x_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2042_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_MVarId_intro(v_mvarId_1970_, v_head_1928_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2033_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v_fst_1976_ = lean_ctor_get(v_a_1975_, 0);
v_snd_1977_ = lean_ctor_get(v_a_1975_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_a_1975_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_1979_ = v_a_1975_;
v_isShared_1980_ = v_isSharedCheck_2033_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_snd_1977_);
lean_inc(v_fst_1976_);
lean_dec(v_a_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2033_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_array_get_size(v_fst_1929_);
v___x_1982_ = l_Lean_Meta_introNCore(v_snd_1977_, v___x_1981_, v_tail_1930_, v___x_1931_, v___x_1965_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2024_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2024_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2024_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2023_; 
v_fst_1987_ = lean_ctor_get(v_a_1983_, 0);
v_snd_1988_ = lean_ctor_get(v_a_1983_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1990_ = v_a_1983_;
v_isShared_1991_ = v_isSharedCheck_2023_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snd_1988_);
lean_inc(v_fst_1987_);
lean_dec(v_a_1983_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2023_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___y_1993_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = l_Array_zip___redArg(v_fst_1929_, v_fst_1987_);
lean_dec(v_fst_1987_);
v___x_2014_ = lean_array_get_size(v___x_2013_);
v___x_2015_ = lean_nat_dec_lt(v___x_1927_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v___x_2013_);
v___y_1993_ = v_fs_1934_;
goto v___jp_1992_;
}
else
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_nat_dec_le(v___x_2014_, v___x_2014_);
if (v___x_2016_ == 0)
{
if (v___x_2015_ == 0)
{
lean_dec_ref(v___x_2013_);
v___y_1993_ = v_fs_1934_;
goto v___jp_1992_;
}
else
{
size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = lean_usize_of_nat(v___x_2014_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2013_, v___x_2017_, v___x_2018_, v_fs_1934_);
lean_dec_ref(v___x_2013_);
v___y_1993_ = v___x_2019_;
goto v___jp_1992_;
}
}
else
{
size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = lean_usize_of_nat(v___x_2014_);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2013_, v___x_2020_, v___x_2021_, v_fs_1934_);
lean_dec_ref(v___x_2013_);
v___y_1993_ = v___x_2022_;
goto v___jp_1992_;
}
}
v___jp_1992_:
{
lean_object* v___x_1995_; 
lean_inc(v_name_1969_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v_snd_1932_);
lean_ctor_set(v___x_1990_, 0, v_name_1969_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_name_1969_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_snd_1932_);
v___x_1995_ = v_reuseFailAlloc_2012_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_mkFVar(v_fst_1976_);
v___x_1999_ = lean_array_push(v___x_1933_, v___x_1998_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 2, v___y_1993_);
lean_ctor_set(v___x_1972_, 1, v___x_1999_);
lean_ctor_set(v___x_1972_, 0, v_snd_1988_);
v___x_2001_ = v___x_1972_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_snd_1988_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v___y_1993_);
v___x_2001_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_name_1969_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_array_push(v___x_1959_, v___x_2003_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_2004_);
lean_ctor_set(v___x_1979_, 0, v___x_1997_);
v___x_2006_ = v___x_1979_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2006_);
v___x_2008_ = v___x_1985_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
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
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_del_object(v___x_1979_);
lean_dec(v_fst_1976_);
lean_del_object(v___x_1972_);
lean_dec(v_name_1969_);
lean_dec_ref(v___x_1959_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
v_a_2025_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1982_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1982_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_del_object(v___x_1972_);
lean_dec(v_name_1969_);
lean_dec_ref(v___x_1959_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
v_a_2034_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1974_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1974_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_alts_1949_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
v_a_2044_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_1963_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_1963_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_alts_1949_);
lean_dec_ref(v_elimApp_1948_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
lean_dec(v_snd_1922_);
v_a_2052_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1962_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1962_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_1943_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
lean_dec(v_snd_1922_);
v_a_2060_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1946_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1946_);
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
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_1943_);
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
lean_dec_ref(v___x_1923_);
lean_dec(v_snd_1922_);
v_a_2068_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1944_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1944_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_fs_1934_);
lean_dec_ref(v___x_1933_);
lean_dec(v_snd_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_head_1928_);
lean_dec_ref(v___x_1923_);
lean_dec(v_snd_1922_);
v_a_2076_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_1942_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_1942_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2084_ = _args[0];
lean_object* v___x_2085_ = _args[1];
lean_object* v_snd_2086_ = _args[2];
lean_object* v___x_2087_ = _args[3];
lean_object* v___x_2088_ = _args[4];
lean_object* v___x_2089_ = _args[5];
lean_object* v_e_2090_ = _args[6];
lean_object* v___x_2091_ = _args[7];
lean_object* v_head_2092_ = _args[8];
lean_object* v_fst_2093_ = _args[9];
lean_object* v_tail_2094_ = _args[10];
lean_object* v___x_2095_ = _args[11];
lean_object* v_snd_2096_ = _args[12];
lean_object* v___x_2097_ = _args[13];
lean_object* v_fs_2098_ = _args[14];
lean_object* v___y_2099_ = _args[15];
lean_object* v___y_2100_ = _args[16];
lean_object* v___y_2101_ = _args[17];
lean_object* v___y_2102_ = _args[18];
lean_object* v___y_2103_ = _args[19];
lean_object* v___y_2104_ = _args[20];
lean_object* v___y_2105_ = _args[21];
_start:
{
uint8_t v___x_19375__boxed_2106_; lean_object* v_res_2107_; 
v___x_19375__boxed_2106_ = lean_unbox(v___x_2095_);
v_res_2107_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2084_, v___x_2085_, v_snd_2086_, v___x_2087_, v___x_2088_, v___x_2089_, v_e_2090_, v___x_2091_, v_head_2092_, v_fst_2093_, v_tail_2094_, v___x_19375__boxed_2106_, v_snd_2096_, v___x_2097_, v_fs_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec_ref(v_fst_2093_);
lean_dec(v___x_2091_);
lean_dec_ref(v_e_2090_);
lean_dec_ref(v___x_2089_);
lean_dec(v___x_2088_);
return v_res_2107_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_2109_ = lean_unsigned_to_nat(76u);
v___x_2110_ = lean_unsigned_to_nat(315u);
v___x_2111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2113_ = l_mkPanicMessageWithDecl(v___x_2112_, v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(uint8_t v___x_2121_, lean_object* v_e_2122_, lean_object* v___x_2123_, lean_object* v_g_2124_, lean_object* v___x_2125_, lean_object* v_fs_2126_, lean_object* v_pat_2127_, lean_object* v_____r_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___y_2140_; uint8_t v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2184_; lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2127_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2184_ = v___x_2191_;
goto v___jp_2183_;
}
else
{
lean_object* v_head_2192_; 
v_head_2192_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_head_2192_);
lean_dec_ref_known(v___x_2190_, 2);
v___y_2184_ = v_head_2192_;
goto v___jp_2183_;
}
v___jp_2136_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0);
v___x_2138_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2137_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
return v___x_2138_;
}
v___jp_2139_:
{
uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_fst_2151_; 
v___x_2143_ = 0;
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1));
v___x_2146_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1, v___x_2143_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 1, v___x_2121_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 2, v___x_2121_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 3, v___x_2121_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 4, v___x_2121_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 5, v___x_2121_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1 + 6, v___x_2121_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_mk_empty_array_with_capacity(v___x_2147_);
lean_inc_ref(v___x_2148_);
v___x_2149_ = lean_array_push(v___x_2148_, v___x_2146_);
v___x_2150_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2142_, v___x_2149_, v___y_2141_, v___x_2144_, v___y_2140_);
lean_dec_ref(v___x_2149_);
v_fst_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_fst_2151_);
if (lean_obj_tag(v_fst_2151_) == 1)
{
lean_object* v_tail_2152_; 
v_tail_2152_ = lean_ctor_get(v_fst_2151_, 1);
lean_inc(v_tail_2152_);
if (lean_obj_tag(v_tail_2152_) == 0)
{
lean_object* v_snd_2153_; lean_object* v_head_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_snd_2153_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_snd_2153_);
lean_dec_ref(v___x_2150_);
v_head_2154_ = lean_ctor_get(v_fst_2151_, 0);
lean_inc(v_head_2154_);
lean_dec_ref_known(v_fst_2151_, 2);
lean_inc_ref(v_e_2122_);
lean_inc_ref(v___x_2148_);
v___x_2155_ = lean_array_push(v___x_2148_, v_e_2122_);
v___x_2156_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2155_, v___x_2123_, v___x_2121_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_MVarId_revert(v_g_2124_, v_a_2157_, v___x_2121_, v___x_2121_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_fst_2160_; lean_object* v_snd_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v_fst_2160_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_fst_2160_);
v_snd_2161_ = lean_ctor_get(v_a_2159_, 1);
lean_inc_n(v_snd_2161_, 2);
lean_dec(v_a_2159_);
v___x_2162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4));
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_box(v___x_2121_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed), 22, 15);
lean_closure_set(v___f_2165_, 0, v___x_2162_);
lean_closure_set(v___f_2165_, 1, v___x_2163_);
lean_closure_set(v___f_2165_, 2, v_snd_2161_);
lean_closure_set(v___f_2165_, 3, v___x_2155_);
lean_closure_set(v___f_2165_, 4, v___x_2147_);
lean_closure_set(v___f_2165_, 5, v___x_2125_);
lean_closure_set(v___f_2165_, 6, v_e_2122_);
lean_closure_set(v___f_2165_, 7, v___x_2144_);
lean_closure_set(v___f_2165_, 8, v_head_2154_);
lean_closure_set(v___f_2165_, 9, v_fst_2160_);
lean_closure_set(v___f_2165_, 10, v_tail_2152_);
lean_closure_set(v___f_2165_, 11, v___x_2164_);
lean_closure_set(v___f_2165_, 12, v_snd_2153_);
lean_closure_set(v___f_2165_, 13, v___x_2148_);
lean_closure_set(v___f_2165_, 14, v_fs_2126_);
v___x_2166_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2161_, v___f_2165_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
return v___x_2166_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v___x_2155_);
lean_dec(v_head_2154_);
lean_dec(v_snd_2153_);
lean_dec_ref(v___x_2148_);
lean_dec(v_fs_2126_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v_e_2122_);
v_a_2167_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2158_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2158_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v___x_2155_);
lean_dec(v_head_2154_);
lean_dec(v_snd_2153_);
lean_dec_ref(v___x_2148_);
lean_dec(v_fs_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v_g_2124_);
lean_dec_ref(v_e_2122_);
v_a_2175_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2156_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2156_);
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
else
{
lean_dec_ref_known(v_fst_2151_, 2);
lean_dec(v_tail_2152_);
lean_dec_ref(v___x_2150_);
lean_dec_ref(v___x_2148_);
lean_dec(v_fs_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v_g_2124_);
lean_dec(v___x_2123_);
lean_dec_ref(v_e_2122_);
goto v___jp_2136_;
}
}
else
{
lean_dec(v_fst_2151_);
lean_dec_ref(v___x_2150_);
lean_dec_ref(v___x_2148_);
lean_dec(v_fs_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v_g_2124_);
lean_dec(v___x_2123_);
lean_dec_ref(v_e_2122_);
goto v___jp_2136_;
}
}
v___jp_2183_:
{
lean_object* v___x_2185_; lean_object* v_fst_2186_; lean_object* v_snd_2187_; lean_object* v_ref_2188_; uint8_t v___x_2189_; 
lean_inc_ref(v___y_2184_);
v___x_2185_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2184_);
v_fst_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_fst_2186_);
v_snd_2187_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_snd_2187_);
lean_dec_ref(v___x_2185_);
v_ref_2188_ = lean_ctor_get(v___y_2184_, 0);
lean_inc(v_ref_2188_);
lean_dec_ref(v___y_2184_);
v___x_2189_ = lean_unbox(v_fst_2186_);
lean_dec(v_fst_2186_);
v___y_2140_ = v_snd_2187_;
v___y_2141_ = v___x_2189_;
v___y_2142_ = v_ref_2188_;
goto v___jp_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v___x_2193_, lean_object* v_e_2194_, lean_object* v___x_2195_, lean_object* v_g_2196_, lean_object* v___x_2197_, lean_object* v_fs_2198_, lean_object* v_pat_2199_, lean_object* v_____r_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v___x_19747__boxed_2208_; lean_object* v_res_2209_; 
v___x_19747__boxed_2208_ = lean_unbox(v___x_2193_);
v_res_2209_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_19747__boxed_2208_, v_e_2194_, v___x_2195_, v_g_2196_, v___x_2197_, v_fs_2198_, v_pat_2199_, v_____r_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2209_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
if (lean_obj_tag(v_x_2211_) == 0)
{
uint8_t v___x_2212_; 
v___x_2212_ = 1;
return v___x_2212_;
}
else
{
uint8_t v___x_2213_; 
v___x_2213_ = 0;
return v___x_2213_;
}
}
else
{
if (lean_obj_tag(v_x_2211_) == 0)
{
uint8_t v___x_2214_; 
v___x_2214_ = 0;
return v___x_2214_;
}
else
{
lean_object* v_val_2215_; lean_object* v_val_2216_; uint8_t v___x_2217_; 
v_val_2215_ = lean_ctor_get(v_x_2210_, 0);
v_val_2216_ = lean_ctor_get(v_x_2211_, 0);
v___x_2217_ = lean_name_eq(v_val_2215_, v_val_2216_);
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v_res_2220_; lean_object* v_r_2221_; 
v_res_2220_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_2218_, v_x_2219_);
lean_dec(v_x_2219_);
lean_dec(v_x_2218_);
v_r_2221_ = lean_box(v_res_2220_);
return v_r_2221_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_2226_ = l_Lean_MessageData_ofFormat(v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
if (lean_obj_tag(v_x_2228_) == 0)
{
return v_x_2227_;
}
else
{
lean_object* v_head_2229_; lean_object* v_tail_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2252_; 
v_head_2229_ = lean_ctor_get(v_x_2228_, 0);
v_tail_2230_ = lean_ctor_get(v_x_2228_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_x_2228_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2232_ = v_x_2228_;
v_isShared_2233_ = v_isSharedCheck_2252_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_tail_2230_);
lean_inc(v_head_2229_);
lean_dec(v_x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2252_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_before_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2250_; 
v_before_2234_ = lean_ctor_get(v_head_2229_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_head_2229_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v_head_2229_, 1);
lean_dec(v_unused_2251_);
v___x_2236_ = v_head_2229_;
v_isShared_2237_ = v_isSharedCheck_2250_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_before_2234_);
lean_dec(v_head_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2250_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 7);
lean_ctor_set(v___x_2236_, 1, v___x_2238_);
lean_ctor_set(v___x_2236_, 0, v_x_2227_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_x_2227_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 7);
lean_ctor_set(v___x_2232_, 1, v___x_2241_);
lean_ctor_set(v___x_2232_, 0, v___x_2240_);
v___x_2243_ = v___x_2232_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = l_Lean_MessageData_ofSyntax(v_before_2234_);
v___x_2245_ = l_Lean_indentD(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2243_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v_x_2227_ = v___x_2246_;
v_x_2228_ = v_tail_2230_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_2253_, lean_object* v_opt_2254_){
_start:
{
lean_object* v_name_2255_; lean_object* v_defValue_2256_; lean_object* v_map_2257_; lean_object* v___x_2258_; 
v_name_2255_ = lean_ctor_get(v_opt_2254_, 0);
v_defValue_2256_ = lean_ctor_get(v_opt_2254_, 1);
v_map_2257_ = lean_ctor_get(v_opts_2253_, 0);
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2257_, v_name_2255_);
if (lean_obj_tag(v___x_2258_) == 0)
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_unbox(v_defValue_2256_);
return v___x_2259_;
}
else
{
lean_object* v_val_2260_; 
v_val_2260_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v___x_2258_, 1);
if (lean_obj_tag(v_val_2260_) == 1)
{
uint8_t v_v_2261_; 
v_v_2261_ = lean_ctor_get_uint8(v_val_2260_, 0);
lean_dec_ref_known(v_val_2260_, 0);
return v_v_2261_;
}
else
{
uint8_t v___x_2262_; 
lean_dec(v_val_2260_);
v___x_2262_ = lean_unbox(v_defValue_2256_);
return v___x_2262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_2263_, lean_object* v_opt_2264_){
_start:
{
uint8_t v_res_2265_; lean_object* v_r_2266_; 
v_res_2265_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_2263_, v_opt_2264_);
lean_dec_ref(v_opt_2264_);
lean_dec_ref(v_opts_2263_);
v_r_2266_ = lean_box(v_res_2265_);
return v_r_2266_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_2271_ = l_Lean_MessageData_ofFormat(v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_2272_, lean_object* v_macroStack_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_options_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_options_2276_ = lean_ctor_get(v___y_2274_, 2);
v___x_2277_ = l_Lean_Elab_pp_macroStack;
v___x_2278_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_options_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
lean_dec(v_macroStack_2273_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_msgData_2272_);
return v___x_2279_;
}
else
{
if (lean_obj_tag(v_macroStack_2273_) == 0)
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_msgData_2272_);
return v___x_2280_;
}
else
{
lean_object* v_head_2281_; lean_object* v_after_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2297_; 
v_head_2281_ = lean_ctor_get(v_macroStack_2273_, 0);
lean_inc(v_head_2281_);
v_after_2282_ = lean_ctor_get(v_head_2281_, 1);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_head_2281_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v_head_2281_, 0);
lean_dec(v_unused_2298_);
v___x_2284_ = v_head_2281_;
v_isShared_2285_ = v_isSharedCheck_2297_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_after_2282_);
lean_dec(v_head_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2297_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 7);
lean_ctor_set(v___x_2284_, 1, v___x_2286_);
lean_ctor_set(v___x_2284_, 0, v_msgData_2272_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_msgData_2272_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_msgData_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2289_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_MessageData_ofSyntax(v_after_2282_);
v___x_2292_ = l_Lean_indentD(v___x_2291_);
v_msgData_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2293_, 0, v___x_2290_);
lean_ctor_set(v_msgData_2293_, 1, v___x_2292_);
v___x_2294_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_2293_, v_macroStack_2273_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_2299_, lean_object* v_macroStack_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_2299_, v_macroStack_2300_, v___y_2301_);
lean_dec_ref(v___y_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_ref_2312_; lean_object* v___x_2313_; lean_object* v_a_2314_; lean_object* v_macroStack_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
v_ref_2312_ = lean_ctor_get(v___y_2309_, 5);
v___x_2313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_2304_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v_macroStack_2315_ = lean_ctor_get(v___y_2305_, 1);
v___x_2316_ = l_Lean_Elab_getBetterRef(v_ref_2312_, v_macroStack_2315_);
lean_inc(v_macroStack_2315_);
v___x_2317_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_2314_, v_macroStack_2315_, v___y_2309_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2316_);
lean_ctor_set(v___x_2322_, 1, v_a_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 1);
lean_ctor_set(v___x_2320_, 0, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2335_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v_e_2342_, lean_object* v_a_2343_, lean_object* v_00_u03b1_2344_, lean_object* v_x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2353_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_2354_ = l_Lean_MessageData_ofExpr(v_e_2342_);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = l_Lean_MessageData_ofExpr(v_a_2343_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_2361_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object* v_e_2363_, lean_object* v_a_2364_, lean_object* v_00_u03b1_2365_, lean_object* v_x_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2363_, v_a_2364_, v_00_u03b1_2365_, v_x_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2375_, lean_object* v_cont_2376_, lean_object* v_g_2377_, lean_object* v_fs_2378_, lean_object* v_clears_2379_, lean_object* v_a_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2375_, v_cont_2376_, v_g_2377_, v_fs_2378_, v_clears_2379_, v_a_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2390_, lean_object* v_g_2391_, lean_object* v_fs_2392_, lean_object* v_clears_2393_, lean_object* v_a_2394_, lean_object* v_cont_2395_, lean_object* v_ref_2396_, lean_object* v_p_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2405_ = lean_box(0);
lean_inc_ref(v_e_2390_);
v___x_2406_ = l_Lean_Expr_mdata___override(v___x_2405_, v_e_2390_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_box(0);
v___x_2409_ = 0;
v___x_2410_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2396_, v___x_2406_, v___x_2407_, v___x_2407_, v___x_2408_, v___x_2409_, v___x_2409_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
lean_dec_ref_known(v___x_2410_, 1);
v___x_2411_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2391_, v_fs_2392_, v_clears_2393_, v_e_2390_, v_a_2394_, v_p_2397_, v_cont_2395_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v_e_2390_);
return v___x_2411_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_p_2397_);
lean_dec_ref(v_cont_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_clears_2393_);
lean_dec(v_fs_2392_);
lean_dec(v_g_2391_);
lean_dec_ref(v_e_2390_);
v_a_2412_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2410_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2420_, lean_object* v_g_2421_, lean_object* v_fs_2422_, lean_object* v_clears_2423_, lean_object* v_a_2424_, lean_object* v_cont_2425_, lean_object* v_ref_2426_, lean_object* v_p_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2420_, v_g_2421_, v_fs_2422_, v_clears_2423_, v_a_2424_, v_cont_2425_, v_ref_2426_, v_p_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2436_, lean_object* v_clears_2437_, lean_object* v_cont_2438_, lean_object* v_a_2439_, lean_object* v_goal_2440_, lean_object* v_ctorName_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
if (lean_obj_tag(v_a_2442_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec_ref(v_goal_2440_);
lean_dec_ref(v_cont_2438_);
lean_dec_ref(v_clears_2437_);
lean_dec(v_fs_2436_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_a_2442_);
lean_ctor_set(v___x_2450_, 1, v_a_2439_);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
else
{
lean_object* v_head_2452_; lean_object* v_tail_2453_; lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2488_; 
v_head_2452_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_head_2452_);
v_tail_2453_ = lean_ctor_get(v_a_2442_, 1);
lean_inc(v_tail_2453_);
lean_dec_ref_known(v_a_2442_, 2);
v_fst_2454_ = lean_ctor_get(v_head_2452_, 0);
v_snd_2455_ = lean_ctor_get(v_head_2452_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_head_2452_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2457_ = v_head_2452_;
v_isShared_2458_ = v_isSharedCheck_2488_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_snd_2455_);
lean_inc(v_fst_2454_);
lean_dec(v_head_2452_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2488_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_fst_2454_);
v___x_2460_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2459_, v_ctorName_2441_);
lean_dec_ref_known(v___x_2459_, 1);
if (v___x_2460_ == 0)
{
lean_del_object(v___x_2457_);
lean_dec(v_snd_2455_);
v_a_2442_ = v_tail_2453_;
goto _start;
}
else
{
lean_object* v_mvarId_2462_; lean_object* v_fields_2463_; lean_object* v_subst_2464_; lean_object* v_fs_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_mvarId_2462_ = lean_ctor_get(v_goal_2440_, 0);
lean_inc(v_mvarId_2462_);
v_fields_2463_ = lean_ctor_get(v_goal_2440_, 1);
lean_inc_ref(v_fields_2463_);
v_subst_2464_ = lean_ctor_get(v_goal_2440_, 2);
lean_inc(v_subst_2464_);
lean_dec_ref(v_goal_2440_);
v_fs_2465_ = l_Lean_Meta_FVarSubst_append(v_fs_2436_, v_subst_2464_);
v___x_2466_ = lean_array_to_list(v_fields_2463_);
v___x_2467_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_snd_2455_, v___x_2466_);
v___x_2468_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2462_, v_fs_2465_, v_clears_2437_, v_a_2439_, v___x_2467_, v_cont_2438_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2479_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2479_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2479_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 1, v_a_2469_);
lean_ctor_set(v___x_2457_, 0, v_tail_2453_);
v___x_2474_ = v___x_2457_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_tail_2453_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2474_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_del_object(v___x_2457_);
lean_dec(v_tail_2453_);
v_a_2480_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2468_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2468_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2489_, lean_object* v_clears_2490_, lean_object* v_cont_2491_, lean_object* v_as_2492_, size_t v_i_2493_, size_t v_stop_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_eq(v_i_2493_, v_stop_2494_);
if (v___x_2503_ == 0)
{
lean_object* v_fst_2504_; lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v_toInductionSubgoal_2507_; lean_object* v_ctorName_2508_; lean_object* v___x_2509_; 
v_fst_2504_ = lean_ctor_get(v_b_2495_, 0);
lean_inc(v_fst_2504_);
v_snd_2505_ = lean_ctor_get(v_b_2495_, 1);
lean_inc(v_snd_2505_);
lean_dec_ref(v_b_2495_);
v___x_2506_ = lean_array_uget_borrowed(v_as_2492_, v_i_2493_);
v_toInductionSubgoal_2507_ = lean_ctor_get(v___x_2506_, 0);
v_ctorName_2508_ = lean_ctor_get(v___x_2506_, 1);
lean_inc_ref(v_toInductionSubgoal_2507_);
lean_inc_ref(v_cont_2491_);
lean_inc_ref(v_clears_2490_);
lean_inc(v_fs_2489_);
v___x_2509_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2489_, v_clears_2490_, v_cont_2491_, v_snd_2505_, v_toInductionSubgoal_2507_, v_ctorName_2508_, v_fst_2504_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; size_t v___x_2511_; size_t v___x_2512_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_add(v_i_2493_, v___x_2511_);
v_i_2493_ = v___x_2512_;
v_b_2495_ = v_a_2510_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2491_);
lean_dec_ref(v_clears_2490_);
lean_dec(v_fs_2489_);
return v___x_2509_;
}
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref(v_cont_2491_);
lean_dec_ref(v_clears_2490_);
lean_dec(v_fs_2489_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_b_2495_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_e_2517_, lean_object* v___y_2518_, lean_object* v_asFVar_2519_, lean_object* v_a_2520_, lean_object* v_fs_2521_, lean_object* v_clears_2522_, lean_object* v_cont_2523_, lean_object* v___x_2524_, lean_object* v_g_2525_, lean_object* v___x_2526_, lean_object* v_pat_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___y_2537_; lean_object* v_fst_2556_; lean_object* v_snd_2557_; lean_object* v___y_2572_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2584_ = lean_box(0);
lean_inc_ref(v_e_2517_);
v___x_2585_ = l_Lean_Expr_mdata___override(v___x_2584_, v_e_2517_);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_box(0);
v___x_2588_ = 0;
lean_inc(v___y_2518_);
v___x_2589_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2518_, v___x_2585_, v___x_2586_, v___x_2586_, v___x_2587_, v___x_2588_, v___x_2588_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2589_, 1);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc_ref(v_e_2517_);
v___x_2590_ = lean_apply_6(v_asFVar_2519_, v_e_2517_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref_known(v___x_2590_, 1);
v___x_2591_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2588_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref_known(v___x_2591_, 1);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc_ref(v_e_2517_);
v___x_2592_ = lean_infer_type(v_e_2517_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_Meta_whnfD(v_a_2593_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = l_Lean_Expr_getAppFn(v_a_2595_);
if (lean_obj_tag(v___x_2596_) == 4)
{
lean_object* v_declName_2597_; lean_object* v___x_2598_; lean_object* v_env_2599_; lean_object* v___x_2600_; 
v_declName_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_declName_2597_);
lean_dec_ref_known(v___x_2596_, 2);
v___x_2598_ = lean_st_ref_get(v___y_2534_);
v_env_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_ref(v_env_2599_);
lean_dec(v___x_2598_);
v___x_2600_ = l_Lean_Environment_find_x3f(v_env_2599_, v_declName_2597_, v___x_2588_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec(v___y_2518_);
v___x_2601_ = lean_box(0);
v___x_2602_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2517_, v_a_2595_, lean_box(0), v___x_2601_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
v___y_2572_ = v___x_2602_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2603_; 
v_val_2603_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2600_, 1);
switch(lean_obj_tag(v_val_2603_))
{
case 4:
{
lean_object* v_val_2604_; uint8_t v_kind_2605_; 
lean_dec(v___y_2518_);
v_val_2604_ = lean_ctor_get(v_val_2603_, 0);
lean_inc_ref(v_val_2604_);
lean_dec_ref_known(v_val_2603_, 1);
v_kind_2605_ = lean_ctor_get_uint8(v_val_2604_, sizeof(void*)*1);
lean_dec_ref(v_val_2604_);
if (v_kind_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_a_2595_);
v___x_2606_ = lean_box(0);
lean_inc(v_fs_2521_);
v___x_2607_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2588_, v_e_2517_, v___x_2524_, v_g_2525_, v___x_2526_, v_fs_2521_, v_pat_2527_, v___x_2606_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
v___y_2572_ = v___x_2607_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_box(0);
lean_inc_ref(v_e_2517_);
v___x_2609_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2517_, v_a_2595_, lean_box(0), v___x_2608_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
lean_inc(v_fs_2521_);
v___x_2611_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2588_, v_e_2517_, v___x_2524_, v_g_2525_, v___x_2526_, v_fs_2521_, v_pat_2527_, v_a_2610_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
v___y_2572_ = v___x_2611_;
goto v___jp_2571_;
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_e_2517_);
v_a_2612_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2609_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2609_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
case 5:
{
lean_object* v_val_2620_; lean_object* v_numParams_2621_; lean_object* v_ctors_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec(v_a_2595_);
lean_dec_ref(v___x_2526_);
lean_dec(v___x_2524_);
v_val_2620_ = lean_ctor_get(v_val_2603_, 0);
lean_inc_ref(v_val_2620_);
lean_dec_ref_known(v_val_2603_, 1);
v_numParams_2621_ = lean_ctor_get(v_val_2620_, 1);
lean_inc(v_numParams_2621_);
v_ctors_2622_ = lean_ctor_get(v_val_2620_, 4);
lean_inc(v_ctors_2622_);
lean_dec_ref(v_val_2620_);
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2624_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2527_);
v___x_2625_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2518_, v_numParams_2621_, v___x_2623_, v_ctors_2622_, v___x_2624_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v_numParams_2621_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v_fst_2627_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_fst_2627_);
v_snd_2628_ = lean_ctor_get(v_a_2626_, 1);
lean_inc(v_snd_2628_);
lean_dec(v_a_2626_);
v___x_2629_ = l_Lean_Expr_fvarId_x21(v_e_2517_);
lean_dec_ref(v_e_2517_);
v___x_2630_ = 1;
v___x_2631_ = l_Lean_MVarId_cases(v_g_2525_, v___x_2629_, v_fst_2627_, v___x_2630_, v___x_2586_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v_fst_2556_ = v_snd_2628_;
v_snd_2557_ = v_a_2632_;
goto v___jp_2555_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_snd_2628_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
v_a_2633_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2631_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_g_2525_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_e_2517_);
v_a_2641_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2625_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2625_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
default: 
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v_val_2603_);
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec(v___y_2518_);
v___x_2649_ = lean_box(0);
v___x_2650_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2517_, v_a_2595_, lean_box(0), v___x_2649_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
v___y_2572_ = v___x_2650_;
goto v___jp_2571_;
}
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec_ref(v___x_2596_);
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec(v___y_2518_);
v___x_2651_ = lean_box(0);
v___x_2652_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2517_, v_a_2595_, lean_box(0), v___x_2651_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
v___y_2572_ = v___x_2652_;
goto v___jp_2571_;
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec(v___y_2518_);
lean_dec_ref(v_e_2517_);
v_a_2653_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2594_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2594_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec(v___y_2518_);
lean_dec_ref(v_e_2517_);
v_a_2661_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2592_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2592_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec(v___y_2518_);
lean_dec_ref(v_e_2517_);
v_a_2669_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2591_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2591_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec(v___y_2518_);
lean_dec_ref(v_e_2517_);
v_a_2677_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2590_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2590_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v_pat_2527_);
lean_dec_ref(v___x_2526_);
lean_dec(v_g_2525_);
lean_dec(v___x_2524_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_asFVar_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v_e_2517_);
v_a_2685_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2589_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2589_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
v___jp_2536_:
{
if (lean_obj_tag(v___y_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
v_a_2538_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v___y_2537_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___y_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_snd_2542_; lean_object* v___x_2544_; 
v_snd_2542_ = lean_ctor_get(v_a_2538_, 1);
lean_inc(v_snd_2542_);
lean_dec(v_a_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v_snd_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_snd_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_a_2547_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___y_2537_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___y_2537_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
v___jp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_array_get_size(v_snd_2557_);
v___x_2560_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
lean_dec_ref(v_snd_2557_);
lean_dec(v_fst_2556_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2520_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
lean_inc(v_a_2520_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_fst_2556_);
lean_ctor_set(v___x_2562_, 1, v_a_2520_);
v___x_2563_ = lean_nat_dec_le(v___x_2559_, v___x_2559_);
if (v___x_2563_ == 0)
{
if (v___x_2560_ == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2562_, 2);
lean_dec_ref(v_snd_2557_);
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2520_);
return v___x_2564_;
}
else
{
size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_a_2520_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = lean_usize_of_nat(v___x_2559_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2521_, v_clears_2522_, v_cont_2523_, v_snd_2557_, v___x_2565_, v___x_2566_, v___x_2562_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec_ref(v_snd_2557_);
v___y_2537_ = v___x_2567_;
goto v___jp_2536_;
}
}
else
{
size_t v___x_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
lean_dec(v_a_2520_);
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = lean_usize_of_nat(v___x_2559_);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2521_, v_clears_2522_, v_cont_2523_, v_snd_2557_, v___x_2568_, v___x_2569_, v___x_2562_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec_ref(v_snd_2557_);
v___y_2537_ = v___x_2570_;
goto v___jp_2536_;
}
}
}
v___jp_2571_:
{
if (lean_obj_tag(v___y_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v_fst_2574_; lean_object* v_snd_2575_; 
v_a_2573_ = lean_ctor_get(v___y_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___y_2572_, 1);
v_fst_2574_ = lean_ctor_get(v_a_2573_, 0);
lean_inc(v_fst_2574_);
v_snd_2575_ = lean_ctor_get(v_a_2573_, 1);
lean_inc(v_snd_2575_);
lean_dec(v_a_2573_);
v_fst_2556_ = v_fst_2574_;
v_snd_2557_ = v_snd_2575_;
goto v___jp_2555_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec_ref(v_cont_2523_);
lean_dec_ref(v_clears_2522_);
lean_dec(v_fs_2521_);
lean_dec(v_a_2520_);
v_a_2576_ = lean_ctor_get(v___y_2572_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___y_2572_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___y_2572_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___y_2572_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_e_2693_ = _args[0];
lean_object* v___y_2694_ = _args[1];
lean_object* v_asFVar_2695_ = _args[2];
lean_object* v_a_2696_ = _args[3];
lean_object* v_fs_2697_ = _args[4];
lean_object* v_clears_2698_ = _args[5];
lean_object* v_cont_2699_ = _args[6];
lean_object* v___x_2700_ = _args[7];
lean_object* v_g_2701_ = _args[8];
lean_object* v___x_2702_ = _args[9];
lean_object* v_pat_2703_ = _args[10];
lean_object* v_x_2704_ = _args[11];
lean_object* v___y_2705_ = _args[12];
lean_object* v___y_2706_ = _args[13];
lean_object* v___y_2707_ = _args[14];
lean_object* v___y_2708_ = _args[15];
lean_object* v___y_2709_ = _args[16];
lean_object* v___y_2710_ = _args[17];
lean_object* v___y_2711_ = _args[18];
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_e_2693_, v___y_2694_, v_asFVar_2695_, v_a_2696_, v_fs_2697_, v_clears_2698_, v_cont_2699_, v___x_2700_, v_g_2701_, v___x_2702_, v_pat_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v_x_2704_);
return v_res_2712_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2717_ = l_Lean_MessageData_ofFormat(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2720_, lean_object* v___f_2721_, lean_object* v_e_2722_, lean_object* v_asFVar_2723_, lean_object* v_g_2724_, lean_object* v_fs_2725_, lean_object* v_cont_2726_, lean_object* v_clears_2727_, lean_object* v_a_2728_, lean_object* v___f_2729_, lean_object* v___f_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
switch(lean_obj_tag(v_pat_2720_))
{
case 1:
{
lean_object* v_a_2738_; 
lean_dec_ref(v___f_2730_);
lean_dec_ref(v___f_2729_);
v_a_2738_ = lean_ctor_get(v_pat_2720_, 1);
lean_inc(v_a_2738_);
if (lean_obj_tag(v_a_2738_) == 1)
{
lean_object* v_pre_2739_; 
v_pre_2739_ = lean_ctor_get(v_a_2738_, 0);
if (lean_obj_tag(v_pre_2739_) == 0)
{
lean_object* v_ref_2740_; lean_object* v_str_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_ref_2740_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2740_);
lean_dec_ref_known(v_pat_2720_, 2);
v_str_2741_ = lean_ctor_get(v_a_2738_, 1);
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2743_ = lean_string_dec_eq(v_str_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2744_ = lean_apply_9(v___f_2721_, v_ref_2740_, v_a_2738_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2744_;
}
else
{
uint8_t v___x_2745_; lean_object* v___x_2746_; 
lean_inc(v_pre_2739_);
lean_dec_ref_known(v_a_2738_, 2);
lean_dec_ref(v___f_2721_);
v___x_2745_ = 0;
v___x_2746_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2745_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec_ref_known(v___x_2746_, 1);
v___x_2747_ = lean_box(0);
lean_inc_ref(v_e_2722_);
v___x_2748_ = l_Lean_Expr_mdata___override(v___x_2747_, v_e_2722_);
v___x_2749_ = lean_box(0);
v___x_2750_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2740_, v___x_2748_, v___x_2749_, v___x_2749_, v_pre_2739_, v___x_2745_, v___x_2745_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; 
lean_dec_ref_known(v___x_2750_, 1);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
v___x_2751_ = lean_apply_6(v_asFVar_2723_, v_e_2722_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2753_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2753_ = l_Lean_Meta_substEq(v_g_2724_, v_a_2752_, v_fs_2725_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v_fst_2755_; lean_object* v_snd_2756_; lean_object* v___x_2757_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v_fst_2755_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_fst_2755_);
v_snd_2756_ = lean_ctor_get(v_a_2754_, 1);
lean_inc(v_snd_2756_);
lean_dec(v_a_2754_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2757_ = lean_apply_11(v_cont_2726_, v_snd_2756_, v_fst_2755_, v_clears_2727_, v_a_2728_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2757_;
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
v_a_2758_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2753_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2753_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
v_a_2766_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2751_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2751_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
v_a_2774_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2750_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2750_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_ref_2740_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
v_a_2782_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2746_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2746_);
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
}
else
{
lean_object* v_ref_2790_; lean_object* v___x_2791_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
v_ref_2790_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2790_);
lean_dec_ref_known(v_pat_2720_, 2);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2791_ = lean_apply_9(v___f_2721_, v_ref_2790_, v_a_2738_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2791_;
}
}
else
{
lean_object* v_ref_2792_; lean_object* v___x_2793_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
v_ref_2792_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2792_);
lean_dec_ref_known(v_pat_2720_, 2);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2793_ = lean_apply_9(v___f_2721_, v_ref_2792_, v_a_2738_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2793_;
}
}
case 2:
{
lean_object* v_ref_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; 
lean_dec_ref(v___f_2730_);
lean_dec_ref(v___f_2729_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v___f_2721_);
v_ref_2794_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2794_);
lean_dec_ref_known(v_pat_2720_, 1);
v___x_2795_ = lean_box(0);
lean_inc_ref(v_e_2722_);
v___x_2796_ = l_Lean_Expr_mdata___override(v___x_2795_, v_e_2722_);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_box(0);
v___x_2799_ = 0;
v___x_2800_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2794_, v___x_2796_, v___x_2797_, v___x_2797_, v___x_2798_, v___x_2799_, v___x_2799_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_dec_ref_known(v___x_2800_, 1);
if (lean_obj_tag(v_e_2722_) == 1)
{
lean_object* v_fvarId_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_fvarId_2801_ = lean_ctor_get(v_e_2722_, 0);
lean_inc(v_fvarId_2801_);
lean_dec_ref_known(v_e_2722_, 1);
v___x_2802_ = lean_array_push(v_clears_2727_, v_fvarId_2801_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2803_ = lean_apply_11(v_cont_2726_, v_g_2724_, v_fs_2725_, v___x_2802_, v_a_2728_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2803_;
}
else
{
lean_object* v___x_2804_; 
lean_dec_ref(v_e_2722_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2804_ = lean_apply_11(v_cont_2726_, v_g_2724_, v_fs_2725_, v_clears_2727_, v_a_2728_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2804_;
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2805_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2800_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2800_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
case 4:
{
lean_object* v_ref_2813_; lean_object* v_a_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; 
lean_dec_ref(v___f_2730_);
lean_dec_ref(v___f_2729_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v___f_2721_);
v_ref_2813_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2813_);
v_a_2814_ = lean_ctor_get(v_pat_2720_, 1);
lean_inc_ref(v_a_2814_);
v_a_2815_ = lean_ctor_get(v_pat_2720_, 2);
lean_inc(v_a_2815_);
lean_dec_ref_known(v_pat_2720_, 3);
v___x_2816_ = lean_box(0);
lean_inc_ref(v_e_2722_);
v___x_2817_ = l_Lean_Expr_mdata___override(v___x_2816_, v_e_2722_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_box(0);
v___x_2820_ = 0;
v___x_2821_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2813_, v___x_2817_, v___x_2818_, v___x_2818_, v___x_2819_, v___x_2820_, v___x_2820_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; 
lean_dec_ref_known(v___x_2821_, 1);
v___x_2822_ = l_Lean_Elab_Term_elabType(v_a_2815_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___x_2844_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc_ref(v_e_2722_);
v___x_2844_ = lean_infer_type(v_e_2722_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_n(v_a_2845_, 2);
lean_dec_ref_known(v___x_2844_, 1);
lean_inc(v_a_2823_);
v___x_2846_ = l_Lean_Meta_isExprDefEq(v_a_2845_, v_a_2823_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; uint8_t v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = lean_unbox(v_a_2847_);
lean_dec(v_a_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2722_);
lean_inc(v_a_2823_);
v___x_2850_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2849_, v_a_2823_, v_a_2845_, v_e_2722_, v___x_2818_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_dec_ref_known(v___x_2850_, 1);
v___y_2825_ = v___y_2731_;
v___y_2826_ = v___y_2732_;
v___y_2827_ = v___y_2733_;
v___y_2828_ = v___y_2734_;
v___y_2829_ = v___y_2735_;
v___y_2830_ = v___y_2736_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_dec(v_a_2845_);
v___y_2825_ = v___y_2731_;
v___y_2826_ = v___y_2732_;
v___y_2827_ = v___y_2733_;
v___y_2828_ = v___y_2734_;
v___y_2829_ = v___y_2735_;
v___y_2830_ = v___y_2736_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_a_2845_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2859_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2846_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2846_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2867_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2844_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2844_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
v___jp_2824_:
{
if (lean_obj_tag(v_e_2722_) == 1)
{
lean_object* v_fvarId_2831_; lean_object* v___x_2832_; 
v_fvarId_2831_ = lean_ctor_get(v_e_2722_, 0);
lean_inc(v_fvarId_2831_);
v___x_2832_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2724_, v_fvarId_2831_, v_a_2823_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2833_, v_fs_2725_, v_clears_2727_, v_e_2722_, v_a_2728_, v_a_2814_, v_cont_2726_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec_ref_known(v_e_2722_, 1);
return v___x_2834_;
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref_known(v_e_2722_, 1);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
v_a_2835_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2832_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2832_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v___x_2843_; 
lean_dec(v_a_2823_);
v___x_2843_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2724_, v_fs_2725_, v_clears_2727_, v_e_2722_, v_a_2728_, v_a_2814_, v_cont_2726_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec_ref(v_e_2722_);
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2875_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2822_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2822_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_e_2722_);
v_a_2883_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2821_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2821_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
case 0:
{
lean_object* v_ref_2891_; lean_object* v_a_2892_; lean_object* v___x_2893_; 
lean_dec_ref(v___f_2730_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
lean_dec_ref(v___f_2721_);
v_ref_2891_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2891_);
v_a_2892_ = lean_ctor_get(v_pat_2720_, 1);
lean_inc_ref(v_a_2892_);
lean_dec_ref_known(v_pat_2720_, 2);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2893_ = lean_apply_9(v___f_2729_, v_ref_2891_, v_a_2892_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2893_;
}
case 6:
{
lean_object* v_a_2894_; 
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
lean_dec_ref(v___f_2721_);
v_a_2894_ = lean_ctor_get(v_pat_2720_, 1);
if (lean_obj_tag(v_a_2894_) == 1)
{
lean_object* v_tail_2895_; 
v_tail_2895_ = lean_ctor_get(v_a_2894_, 1);
if (lean_obj_tag(v_tail_2895_) == 0)
{
lean_object* v_ref_2896_; lean_object* v_head_2897_; lean_object* v___x_2898_; 
lean_inc_ref(v_a_2894_);
lean_dec_ref(v___f_2730_);
v_ref_2896_ = lean_ctor_get(v_pat_2720_, 0);
lean_inc(v_ref_2896_);
lean_dec_ref_known(v_pat_2720_, 2);
v_head_2897_ = lean_ctor_get(v_a_2894_, 0);
lean_inc(v_head_2897_);
lean_dec_ref_known(v_a_2894_, 2);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2898_ = lean_apply_9(v___f_2729_, v_ref_2896_, v_head_2897_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2898_;
}
else
{
lean_object* v___x_2899_; 
lean_dec_ref(v___f_2729_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2899_ = lean_apply_8(v___f_2730_, v_pat_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2899_;
}
}
else
{
lean_object* v___x_2900_; 
lean_dec_ref(v___f_2729_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2900_ = lean_apply_8(v___f_2730_, v_pat_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2900_;
}
}
default: 
{
lean_object* v___x_2901_; 
lean_dec_ref(v___f_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_clears_2727_);
lean_dec_ref(v_cont_2726_);
lean_dec(v_fs_2725_);
lean_dec(v_g_2724_);
lean_dec_ref(v_asFVar_2723_);
lean_dec_ref(v_e_2722_);
lean_dec_ref(v___f_2721_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2901_ = lean_apply_8(v___f_2730_, v_pat_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2902_ = _args[0];
lean_object* v___f_2903_ = _args[1];
lean_object* v_e_2904_ = _args[2];
lean_object* v_asFVar_2905_ = _args[3];
lean_object* v_g_2906_ = _args[4];
lean_object* v_fs_2907_ = _args[5];
lean_object* v_cont_2908_ = _args[6];
lean_object* v_clears_2909_ = _args[7];
lean_object* v_a_2910_ = _args[8];
lean_object* v___f_2911_ = _args[9];
lean_object* v___f_2912_ = _args[10];
lean_object* v___y_2913_ = _args[11];
lean_object* v___y_2914_ = _args[12];
lean_object* v___y_2915_ = _args[13];
lean_object* v___y_2916_ = _args[14];
lean_object* v___y_2917_ = _args[15];
lean_object* v___y_2918_ = _args[16];
lean_object* v___y_2919_ = _args[17];
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2902_, v___f_2903_, v_e_2904_, v_asFVar_2905_, v_g_2906_, v_fs_2907_, v_cont_2908_, v_clears_2909_, v_a_2910_, v___f_2911_, v___f_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2921_, lean_object* v_fs_2922_, lean_object* v_clears_2923_, lean_object* v_e_2924_, lean_object* v_a_2925_, lean_object* v_pat_2926_, lean_object* v_cont_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_asFVar_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v_e_2938_; lean_object* v___f_2939_; lean_object* v___f_2940_; lean_object* v___y_2942_; lean_object* v_ref_2964_; 
v_asFVar_2935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2936_ = lean_box(1);
v___x_2937_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2922_, 3);
v_e_2938_ = l_Lean_Meta_FVarSubst_apply(v_fs_2922_, v_e_2924_);
lean_inc_n(v_a_2925_, 2);
lean_inc_ref_n(v_clears_2923_, 2);
lean_inc_n(v_g_2921_, 2);
lean_inc_ref_n(v_cont_2927_, 2);
lean_inc_ref_n(v_e_2938_, 2);
v___f_2939_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2939_, 0, v_e_2938_);
lean_closure_set(v___f_2939_, 1, v_cont_2927_);
lean_closure_set(v___f_2939_, 2, v_g_2921_);
lean_closure_set(v___f_2939_, 3, v_fs_2922_);
lean_closure_set(v___f_2939_, 4, v_clears_2923_);
lean_closure_set(v___f_2939_, 5, v_a_2925_);
v___f_2940_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2940_, 0, v_e_2938_);
lean_closure_set(v___f_2940_, 1, v_g_2921_);
lean_closure_set(v___f_2940_, 2, v_fs_2922_);
lean_closure_set(v___f_2940_, 3, v_clears_2923_);
lean_closure_set(v___f_2940_, 4, v_a_2925_);
lean_closure_set(v___f_2940_, 5, v_cont_2927_);
v_ref_2964_ = lean_ctor_get(v_pat_2926_, 0);
lean_inc(v_ref_2964_);
v___y_2942_ = v_ref_2964_;
goto v___jp_2941_;
v___jp_2941_:
{
lean_object* v_fileName_2943_; lean_object* v_fileMap_2944_; lean_object* v_options_2945_; lean_object* v_currRecDepth_2946_; lean_object* v_maxRecDepth_2947_; lean_object* v_ref_2948_; lean_object* v_currNamespace_2949_; lean_object* v_openDecls_2950_; lean_object* v_initHeartbeats_2951_; lean_object* v_maxHeartbeats_2952_; lean_object* v_quotContext_2953_; lean_object* v_currMacroScope_2954_; uint8_t v_diag_2955_; lean_object* v_cancelTk_x3f_2956_; uint8_t v_suppressElabErrors_2957_; lean_object* v_inheritedTraceOptions_2958_; lean_object* v___f_2959_; lean_object* v___y_2960_; lean_object* v_ref_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_fileName_2943_ = lean_ctor_get(v_a_2932_, 0);
v_fileMap_2944_ = lean_ctor_get(v_a_2932_, 1);
v_options_2945_ = lean_ctor_get(v_a_2932_, 2);
v_currRecDepth_2946_ = lean_ctor_get(v_a_2932_, 3);
v_maxRecDepth_2947_ = lean_ctor_get(v_a_2932_, 4);
v_ref_2948_ = lean_ctor_get(v_a_2932_, 5);
v_currNamespace_2949_ = lean_ctor_get(v_a_2932_, 6);
v_openDecls_2950_ = lean_ctor_get(v_a_2932_, 7);
v_initHeartbeats_2951_ = lean_ctor_get(v_a_2932_, 8);
v_maxHeartbeats_2952_ = lean_ctor_get(v_a_2932_, 9);
v_quotContext_2953_ = lean_ctor_get(v_a_2932_, 10);
v_currMacroScope_2954_ = lean_ctor_get(v_a_2932_, 11);
v_diag_2955_ = lean_ctor_get_uint8(v_a_2932_, sizeof(void*)*14);
v_cancelTk_x3f_2956_ = lean_ctor_get(v_a_2932_, 12);
v_suppressElabErrors_2957_ = lean_ctor_get_uint8(v_a_2932_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2958_ = lean_ctor_get(v_a_2932_, 13);
lean_inc_ref(v_pat_2926_);
lean_inc_n(v_g_2921_, 2);
lean_inc_ref(v_cont_2927_);
lean_inc_ref(v_clears_2923_);
lean_inc(v_fs_2922_);
lean_inc(v_a_2925_);
lean_inc(v___y_2942_);
lean_inc_ref(v_e_2938_);
v___f_2959_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2959_, 0, v_e_2938_);
lean_closure_set(v___f_2959_, 1, v___y_2942_);
lean_closure_set(v___f_2959_, 2, v_asFVar_2935_);
lean_closure_set(v___f_2959_, 3, v_a_2925_);
lean_closure_set(v___f_2959_, 4, v_fs_2922_);
lean_closure_set(v___f_2959_, 5, v_clears_2923_);
lean_closure_set(v___f_2959_, 6, v_cont_2927_);
lean_closure_set(v___f_2959_, 7, v___x_2936_);
lean_closure_set(v___f_2959_, 8, v_g_2921_);
lean_closure_set(v___f_2959_, 9, v___x_2937_);
lean_closure_set(v___f_2959_, 10, v_pat_2926_);
v___y_2960_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2960_, 0, v_pat_2926_);
lean_closure_set(v___y_2960_, 1, v___f_2939_);
lean_closure_set(v___y_2960_, 2, v_e_2938_);
lean_closure_set(v___y_2960_, 3, v_asFVar_2935_);
lean_closure_set(v___y_2960_, 4, v_g_2921_);
lean_closure_set(v___y_2960_, 5, v_fs_2922_);
lean_closure_set(v___y_2960_, 6, v_cont_2927_);
lean_closure_set(v___y_2960_, 7, v_clears_2923_);
lean_closure_set(v___y_2960_, 8, v_a_2925_);
lean_closure_set(v___y_2960_, 9, v___f_2940_);
lean_closure_set(v___y_2960_, 10, v___f_2959_);
v_ref_2961_ = l_Lean_replaceRef(v___y_2942_, v_ref_2948_);
lean_dec(v___y_2942_);
lean_inc_ref(v_inheritedTraceOptions_2958_);
lean_inc(v_cancelTk_x3f_2956_);
lean_inc(v_currMacroScope_2954_);
lean_inc(v_quotContext_2953_);
lean_inc(v_maxHeartbeats_2952_);
lean_inc(v_initHeartbeats_2951_);
lean_inc(v_openDecls_2950_);
lean_inc(v_currNamespace_2949_);
lean_inc(v_maxRecDepth_2947_);
lean_inc(v_currRecDepth_2946_);
lean_inc_ref(v_options_2945_);
lean_inc_ref(v_fileMap_2944_);
lean_inc_ref(v_fileName_2943_);
v___x_2962_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2962_, 0, v_fileName_2943_);
lean_ctor_set(v___x_2962_, 1, v_fileMap_2944_);
lean_ctor_set(v___x_2962_, 2, v_options_2945_);
lean_ctor_set(v___x_2962_, 3, v_currRecDepth_2946_);
lean_ctor_set(v___x_2962_, 4, v_maxRecDepth_2947_);
lean_ctor_set(v___x_2962_, 5, v_ref_2961_);
lean_ctor_set(v___x_2962_, 6, v_currNamespace_2949_);
lean_ctor_set(v___x_2962_, 7, v_openDecls_2950_);
lean_ctor_set(v___x_2962_, 8, v_initHeartbeats_2951_);
lean_ctor_set(v___x_2962_, 9, v_maxHeartbeats_2952_);
lean_ctor_set(v___x_2962_, 10, v_quotContext_2953_);
lean_ctor_set(v___x_2962_, 11, v_currMacroScope_2954_);
lean_ctor_set(v___x_2962_, 12, v_cancelTk_x3f_2956_);
lean_ctor_set(v___x_2962_, 13, v_inheritedTraceOptions_2958_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*14, v_diag_2955_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*14 + 1, v_suppressElabErrors_2957_);
v___x_2963_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2921_, v___y_2960_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v___x_2962_, v_a_2933_);
lean_dec_ref_known(v___x_2962_, 14);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2965_, lean_object* v_fs_2966_, lean_object* v_clears_2967_, lean_object* v_a_2968_, lean_object* v_pats_2969_, lean_object* v_cont_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
if (lean_obj_tag(v_pats_2969_) == 0)
{
lean_object* v___x_2978_; 
lean_inc(v_a_2976_);
lean_inc_ref(v_a_2975_);
lean_inc(v_a_2974_);
lean_inc_ref(v_a_2973_);
lean_inc(v_a_2972_);
lean_inc_ref(v_a_2971_);
v___x_2978_ = lean_apply_11(v_cont_2970_, v_g_2965_, v_fs_2966_, v_clears_2967_, v_a_2968_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, lean_box(0));
return v___x_2978_;
}
else
{
lean_object* v_head_2979_; lean_object* v_tail_2980_; lean_object* v_fst_2981_; lean_object* v_snd_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; 
v_head_2979_ = lean_ctor_get(v_pats_2969_, 0);
lean_inc(v_head_2979_);
v_tail_2980_ = lean_ctor_get(v_pats_2969_, 1);
lean_inc(v_tail_2980_);
lean_dec_ref_known(v_pats_2969_, 2);
v_fst_2981_ = lean_ctor_get(v_head_2979_, 0);
lean_inc(v_fst_2981_);
v_snd_2982_ = lean_ctor_get(v_head_2979_, 1);
lean_inc(v_snd_2982_);
lean_dec(v_head_2979_);
v___f_2983_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2983_, 0, v_tail_2980_);
lean_closure_set(v___f_2983_, 1, v_cont_2970_);
v___x_2984_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2965_, v_fs_2966_, v_clears_2967_, v_snd_2982_, v_a_2968_, v_fst_2981_, v___f_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_snd_2982_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2985_, lean_object* v_cont_2986_, lean_object* v_g_2987_, lean_object* v_fs_2988_, lean_object* v_clears_2989_, lean_object* v_a_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2987_, v_fs_2988_, v_clears_2989_, v_a_2990_, v_tail_2985_, v_cont_2986_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2999_, lean_object* v_fs_3000_, lean_object* v_clears_3001_, lean_object* v_a_3002_, lean_object* v_pats_3003_, lean_object* v_cont_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2999_, v_fs_3000_, v_clears_3001_, v_a_3002_, v_pats_3003_, v_cont_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_3013_, lean_object* v_clears_3014_, lean_object* v_cont_3015_, lean_object* v_as_3016_, lean_object* v_i_3017_, lean_object* v_stop_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
size_t v_i_boxed_3027_; size_t v_stop_boxed_3028_; lean_object* v_res_3029_; 
v_i_boxed_3027_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_stop_boxed_3028_ = lean_unbox_usize(v_stop_3018_);
lean_dec(v_stop_3018_);
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3013_, v_clears_3014_, v_cont_3015_, v_as_3016_, v_i_boxed_3027_, v_stop_boxed_3028_, v_b_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v_as_3016_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_3030_, lean_object* v_clears_3031_, lean_object* v_cont_3032_, lean_object* v_a_3033_, lean_object* v_goal_3034_, lean_object* v_ctorName_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3030_, v_clears_3031_, v_cont_3032_, v_a_3033_, v_goal_3034_, v_ctorName_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_ctorName_3035_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3045_, lean_object* v_fs_3046_, lean_object* v_clears_3047_, lean_object* v_e_3048_, lean_object* v_a_3049_, lean_object* v_pat_3050_, lean_object* v_cont_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3045_, v_fs_3046_, v_clears_3047_, v_e_3048_, v_a_3049_, v_pat_3050_, v_cont_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec_ref(v_e_3048_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3060_, lean_object* v_g_3061_, lean_object* v_fs_3062_, lean_object* v_clears_3063_, lean_object* v_a_3064_, lean_object* v_pats_3065_, lean_object* v_cont_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3061_, v_fs_3062_, v_clears_3063_, v_a_3064_, v_pats_3065_, v_cont_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3075_, lean_object* v_g_3076_, lean_object* v_fs_3077_, lean_object* v_clears_3078_, lean_object* v_a_3079_, lean_object* v_pats_3080_, lean_object* v_cont_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3075_, v_g_3076_, v_fs_3077_, v_clears_3078_, v_a_3079_, v_pats_3080_, v_cont_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3090_, lean_object* v_fs_3091_, lean_object* v_clears_3092_, lean_object* v_cont_3093_, lean_object* v_a_3094_, lean_object* v_goal_3095_, lean_object* v_ctorName_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3091_, v_clears_3092_, v_cont_3093_, v_a_3094_, v_goal_3095_, v_ctorName_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_fs_3107_, lean_object* v_clears_3108_, lean_object* v_cont_3109_, lean_object* v_a_3110_, lean_object* v_goal_3111_, lean_object* v_ctorName_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3106_, v_fs_3107_, v_clears_3108_, v_cont_3109_, v_a_3110_, v_goal_3111_, v_ctorName_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_ctorName_3112_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3122_, lean_object* v_mvarId_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3123_, v_x_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_mvarId_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3133_, v_mvarId_3134_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3144_, lean_object* v_g_3145_, lean_object* v_fs_3146_, lean_object* v_clears_3147_, lean_object* v_e_3148_, lean_object* v_a_3149_, lean_object* v_pat_3150_, lean_object* v_cont_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3145_, v_fs_3146_, v_clears_3147_, v_e_3148_, v_a_3149_, v_pat_3150_, v_cont_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3160_, lean_object* v_g_3161_, lean_object* v_fs_3162_, lean_object* v_clears_3163_, lean_object* v_e_3164_, lean_object* v_a_3165_, lean_object* v_pat_3166_, lean_object* v_cont_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3160_, v_g_3161_, v_fs_3162_, v_clears_3163_, v_e_3164_, v_a_3165_, v_pat_3166_, v_cont_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec_ref(v_e_3164_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3176_, lean_object* v_fs_3177_, lean_object* v_clears_3178_, lean_object* v_cont_3179_, lean_object* v_as_3180_, size_t v_i_3181_, size_t v_stop_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3177_, v_clears_3178_, v_cont_3179_, v_as_3180_, v_i_3181_, v_stop_3182_, v_b_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_fs_3193_, lean_object* v_clears_3194_, lean_object* v_cont_3195_, lean_object* v_as_3196_, lean_object* v_i_3197_, lean_object* v_stop_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
size_t v_i_boxed_3207_; size_t v_stop_boxed_3208_; lean_object* v_res_3209_; 
v_i_boxed_3207_ = lean_unbox_usize(v_i_3197_);
lean_dec(v_i_3197_);
v_stop_boxed_3208_ = lean_unbox_usize(v_stop_3198_);
lean_dec(v_stop_3198_);
v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3192_, v_fs_3193_, v_clears_3194_, v_cont_3195_, v_as_3196_, v_i_boxed_3207_, v_stop_boxed_3208_, v_b_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec_ref(v_as_3196_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3210_, lean_object* v_val_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3210_, v_val_3211_, v___y_3215_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3220_, lean_object* v_val_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3220_, v_val_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3230_, lean_object* v_msg_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3240_, v_msg_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3251_, v_x_3252_, v_x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3255_, lean_object* v_macroStack_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3255_, v_macroStack_3256_, v___y_3261_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3265_, lean_object* v_macroStack_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3265_, v_macroStack_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3275_, lean_object* v_x_3276_, size_t v_x_3277_, size_t v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3276_, v_x_3277_, v_x_3278_, v_x_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
size_t v_x_21337__boxed_3288_; size_t v_x_21338__boxed_3289_; lean_object* v_res_3290_; 
v_x_21337__boxed_3288_ = lean_unbox_usize(v_x_3284_);
lean_dec(v_x_3284_);
v_x_21338__boxed_3289_ = lean_unbox_usize(v_x_3285_);
lean_dec(v_x_3285_);
v_res_3290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3282_, v_x_3283_, v_x_21337__boxed_3288_, v_x_21338__boxed_3289_, v_x_3286_, v_x_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3291_, lean_object* v_n_3292_, lean_object* v_k_3293_, lean_object* v_v_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3292_, v_k_3293_, v_v_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3296_, size_t v_depth_3297_, lean_object* v_keys_3298_, lean_object* v_vals_3299_, lean_object* v_heq_3300_, lean_object* v_i_3301_, lean_object* v_entries_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3297_, v_keys_3298_, v_vals_3299_, v_i_3301_, v_entries_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_depth_3305_, lean_object* v_keys_3306_, lean_object* v_vals_3307_, lean_object* v_heq_3308_, lean_object* v_i_3309_, lean_object* v_entries_3310_){
_start:
{
size_t v_depth_boxed_3311_; lean_object* v_res_3312_; 
v_depth_boxed_3311_ = lean_unbox_usize(v_depth_3305_);
lean_dec(v_depth_3305_);
v_res_3312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3304_, v_depth_boxed_3311_, v_keys_3306_, v_vals_3307_, v_heq_3308_, v_i_3309_, v_entries_3310_);
lean_dec_ref(v_vals_3307_);
lean_dec_ref(v_keys_3306_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3314_, v_x_3315_, v_x_3316_, v_x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3319_, lean_object* v_as_3320_, size_t v_i_3321_, size_t v_stop_3322_){
_start:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_usize_dec_eq(v_i_3321_, v_stop_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = lean_array_uget_borrowed(v_as_3320_, v_i_3321_);
v___x_3325_ = l_Lean_instBEqFVarId_beq(v_a_3319_, v___x_3324_);
if (v___x_3325_ == 0)
{
size_t v___x_3326_; size_t v___x_3327_; 
v___x_3326_ = ((size_t)1ULL);
v___x_3327_ = lean_usize_add(v_i_3321_, v___x_3326_);
v_i_3321_ = v___x_3327_;
goto _start;
}
else
{
return v___x_3325_;
}
}
else
{
uint8_t v___x_3329_; 
v___x_3329_ = 0;
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3330_, lean_object* v_as_3331_, lean_object* v_i_3332_, lean_object* v_stop_3333_){
_start:
{
size_t v_i_boxed_3334_; size_t v_stop_boxed_3335_; uint8_t v_res_3336_; lean_object* v_r_3337_; 
v_i_boxed_3334_ = lean_unbox_usize(v_i_3332_);
lean_dec(v_i_3332_);
v_stop_boxed_3335_ = lean_unbox_usize(v_stop_3333_);
lean_dec(v_stop_3333_);
v_res_3336_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3330_, v_as_3331_, v_i_boxed_3334_, v_stop_boxed_3335_);
lean_dec_ref(v_as_3331_);
lean_dec(v_a_3330_);
v_r_3337_ = lean_box(v_res_3336_);
return v_r_3337_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = lean_array_get_size(v_as_3338_);
v___x_3342_ = lean_nat_dec_lt(v___x_3340_, v___x_3341_);
if (v___x_3342_ == 0)
{
return v___x_3342_;
}
else
{
if (v___x_3342_ == 0)
{
return v___x_3342_;
}
else
{
size_t v___x_3343_; size_t v___x_3344_; uint8_t v___x_3345_; 
v___x_3343_ = ((size_t)0ULL);
v___x_3344_ = lean_usize_of_nat(v___x_3341_);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3339_, v_as_3338_, v___x_3343_, v___x_3344_);
return v___x_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3346_, lean_object* v_a_3347_){
_start:
{
uint8_t v_res_3348_; lean_object* v_r_3349_; 
v_res_3348_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_as_3346_);
v_r_3349_ = lean_box(v_res_3348_);
return v_r_3349_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v___x_3352_; 
v___x_3352_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3350_, v___y_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v_res_3355_; lean_object* v_r_3356_; 
v_res_3355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec(v_snd_3353_);
v_r_3356_ = lean_box(v_res_3355_);
return v_r_3356_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3357_){
_start:
{
uint8_t v___x_3358_; 
v___x_3358_ = 0;
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3359_){
_start:
{
uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3359_);
lean_dec(v_x_3359_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_unsigned_to_nat(16u);
v___x_3365_ = lean_mk_array(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v___x_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3369_, size_t v_sz_3370_, size_t v_i_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_){
_start:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_usize_dec_lt(v_i_3371_, v_sz_3370_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_b_3372_);
return v___x_3376_;
}
else
{
lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3508_; 
v_snd_3377_ = lean_ctor_get(v_b_3372_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_b_3372_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; 
v_unused_3509_ = lean_ctor_get(v_b_3372_, 0);
lean_dec(v_unused_3509_);
v___x_3379_ = v_b_3372_;
v_isShared_3380_ = v_isSharedCheck_3508_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_dec(v_b_3372_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3508_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v_a_3383_; lean_object* v_a_3390_; 
v___x_3381_ = lean_box(0);
v_a_3390_ = lean_array_uget_borrowed(v_as_3369_, v_i_3371_);
if (lean_obj_tag(v_a_3390_) == 0)
{
v_a_3383_ = v_snd_3377_;
goto v___jp_3382_;
}
else
{
lean_object* v_val_3391_; uint8_t v_a_3393_; lean_object* v___f_3396_; lean_object* v___f_3397_; 
v_val_3391_ = lean_ctor_get(v_a_3390_, 0);
v___f_3396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3377_);
v___f_3397_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3397_, 0, v_snd_3377_);
if (lean_obj_tag(v_val_3391_) == 0)
{
lean_object* v_type_3398_; lean_object* v___x_3399_; uint8_t v_fst_3401_; lean_object* v_mctx_3402_; lean_object* v___y_3418_; lean_object* v_mctx_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_type_3398_ = lean_ctor_get(v_val_3391_, 3);
v___x_3399_ = lean_st_ref_get(v___y_3373_);
v_mctx_3423_ = lean_ctor_get(v___x_3399_, 0);
lean_inc_ref_n(v_mctx_3423_, 2);
lean_dec(v___x_3399_);
v___x_3424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v_mctx_3423_);
v___x_3426_ = l_Lean_Expr_hasFVar(v_type_3398_);
if (v___x_3426_ == 0)
{
uint8_t v___x_3427_; 
v___x_3427_ = l_Lean_Expr_hasMVar(v_type_3398_);
if (v___x_3427_ == 0)
{
lean_dec_ref_known(v___x_3425_, 2);
lean_dec_ref(v___f_3397_);
v_fst_3401_ = v___x_3427_;
v_mctx_3402_ = v_mctx_3423_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3428_; 
lean_dec_ref(v_mctx_3423_);
lean_inc_ref(v_type_3398_);
v___x_3428_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3398_, v___x_3425_);
v___y_3418_ = v___x_3428_;
goto v___jp_3417_;
}
}
else
{
lean_object* v___x_3429_; 
lean_dec_ref(v_mctx_3423_);
lean_inc_ref(v_type_3398_);
v___x_3429_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3398_, v___x_3425_);
v___y_3418_ = v___x_3429_;
goto v___jp_3417_;
}
v___jp_3400_:
{
lean_object* v___x_3403_; lean_object* v_cache_3404_; lean_object* v_zetaDeltaFVarIds_3405_; lean_object* v_postponed_3406_; lean_object* v_diag_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3415_; 
v___x_3403_ = lean_st_ref_take(v___y_3373_);
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
v___x_3413_ = lean_st_ref_put(v___y_3373_, v___x_3412_);
v_a_3393_ = v_fst_3401_;
goto v___jp_3392_;
}
}
}
v___jp_3417_:
{
lean_object* v_snd_3419_; lean_object* v_fst_3420_; lean_object* v_mctx_3421_; uint8_t v___x_3422_; 
v_snd_3419_ = lean_ctor_get(v___y_3418_, 1);
lean_inc(v_snd_3419_);
v_fst_3420_ = lean_ctor_get(v___y_3418_, 0);
lean_inc(v_fst_3420_);
lean_dec_ref(v___y_3418_);
v_mctx_3421_ = lean_ctor_get(v_snd_3419_, 1);
lean_inc_ref(v_mctx_3421_);
lean_dec(v_snd_3419_);
v___x_3422_ = lean_unbox(v_fst_3420_);
lean_dec(v_fst_3420_);
v_fst_3401_ = v___x_3422_;
v_mctx_3402_ = v_mctx_3421_;
goto v___jp_3400_;
}
}
else
{
uint8_t v_nondep_3430_; 
v_nondep_3430_ = lean_ctor_get_uint8(v_val_3391_, sizeof(void*)*5);
if (v_nondep_3430_ == 0)
{
lean_object* v_type_3431_; lean_object* v_value_3432_; lean_object* v___x_3433_; uint8_t v_fst_3435_; lean_object* v_snd_3436_; lean_object* v___y_3453_; uint8_t v_fst_3458_; lean_object* v_snd_3459_; lean_object* v___y_3465_; lean_object* v_mctx_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v_type_3431_ = lean_ctor_get(v_val_3391_, 3);
v_value_3432_ = lean_ctor_get(v_val_3391_, 4);
v___x_3433_ = lean_st_ref_get(v___y_3373_);
v_mctx_3469_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_mctx_3469_);
lean_dec(v___x_3433_);
v___x_3470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_mctx_3469_);
v___x_3472_ = l_Lean_Expr_hasFVar(v_type_3431_);
if (v___x_3472_ == 0)
{
uint8_t v___x_3473_; 
v___x_3473_ = l_Lean_Expr_hasMVar(v_type_3431_);
if (v___x_3473_ == 0)
{
v_fst_3458_ = v___x_3473_;
v_snd_3459_ = v___x_3471_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3474_; 
lean_inc_ref(v_type_3431_);
lean_inc_ref(v___f_3397_);
v___x_3474_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3431_, v___x_3471_);
v___y_3465_ = v___x_3474_;
goto v___jp_3464_;
}
}
else
{
lean_object* v___x_3475_; 
lean_inc_ref(v_type_3431_);
lean_inc_ref(v___f_3397_);
v___x_3475_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3431_, v___x_3471_);
v___y_3465_ = v___x_3475_;
goto v___jp_3464_;
}
v___jp_3434_:
{
lean_object* v_mctx_3437_; lean_object* v___x_3438_; lean_object* v_cache_3439_; lean_object* v_zetaDeltaFVarIds_3440_; lean_object* v_postponed_3441_; lean_object* v_diag_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3450_; 
v_mctx_3437_ = lean_ctor_get(v_snd_3436_, 1);
lean_inc_ref(v_mctx_3437_);
lean_dec_ref(v_snd_3436_);
v___x_3438_ = lean_st_ref_take(v___y_3373_);
v_cache_3439_ = lean_ctor_get(v___x_3438_, 1);
v_zetaDeltaFVarIds_3440_ = lean_ctor_get(v___x_3438_, 2);
v_postponed_3441_ = lean_ctor_get(v___x_3438_, 3);
v_diag_3442_ = lean_ctor_get(v___x_3438_, 4);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3451_);
v___x_3444_ = v___x_3438_;
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_diag_3442_);
lean_inc(v_postponed_3441_);
lean_inc(v_zetaDeltaFVarIds_3440_);
lean_inc(v_cache_3439_);
lean_dec(v___x_3438_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v_mctx_3437_);
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_mctx_3437_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_cache_3439_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_zetaDeltaFVarIds_3440_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_postponed_3441_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_diag_3442_);
v___x_3447_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_st_ref_put(v___y_3373_, v___x_3447_);
v_a_3393_ = v_fst_3435_;
goto v___jp_3392_;
}
}
}
v___jp_3452_:
{
lean_object* v_fst_3454_; lean_object* v_snd_3455_; uint8_t v___x_3456_; 
v_fst_3454_ = lean_ctor_get(v___y_3453_, 0);
lean_inc(v_fst_3454_);
v_snd_3455_ = lean_ctor_get(v___y_3453_, 1);
lean_inc(v_snd_3455_);
lean_dec_ref(v___y_3453_);
v___x_3456_ = lean_unbox(v_fst_3454_);
lean_dec(v_fst_3454_);
v_fst_3435_ = v___x_3456_;
v_snd_3436_ = v_snd_3455_;
goto v___jp_3434_;
}
v___jp_3457_:
{
if (v_fst_3458_ == 0)
{
uint8_t v___x_3460_; 
v___x_3460_ = l_Lean_Expr_hasFVar(v_value_3432_);
if (v___x_3460_ == 0)
{
uint8_t v___x_3461_; 
v___x_3461_ = l_Lean_Expr_hasMVar(v_value_3432_);
if (v___x_3461_ == 0)
{
lean_dec_ref(v___f_3397_);
v_fst_3435_ = v___x_3461_;
v_snd_3436_ = v_snd_3459_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3462_; 
lean_inc_ref(v_value_3432_);
v___x_3462_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_value_3432_, v_snd_3459_);
v___y_3453_ = v___x_3462_;
goto v___jp_3452_;
}
}
else
{
lean_object* v___x_3463_; 
lean_inc_ref(v_value_3432_);
v___x_3463_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_value_3432_, v_snd_3459_);
v___y_3453_ = v___x_3463_;
goto v___jp_3452_;
}
}
else
{
lean_dec_ref(v___f_3397_);
v_fst_3435_ = v_fst_3458_;
v_snd_3436_ = v_snd_3459_;
goto v___jp_3434_;
}
}
v___jp_3464_:
{
lean_object* v_fst_3466_; lean_object* v_snd_3467_; uint8_t v___x_3468_; 
v_fst_3466_ = lean_ctor_get(v___y_3465_, 0);
lean_inc(v_fst_3466_);
v_snd_3467_ = lean_ctor_get(v___y_3465_, 1);
lean_inc(v_snd_3467_);
lean_dec_ref(v___y_3465_);
v___x_3468_ = lean_unbox(v_fst_3466_);
lean_dec(v_fst_3466_);
v_fst_3458_ = v___x_3468_;
v_snd_3459_ = v_snd_3467_;
goto v___jp_3457_;
}
}
else
{
lean_object* v_type_3476_; lean_object* v___x_3477_; uint8_t v_fst_3479_; lean_object* v_mctx_3480_; lean_object* v___y_3496_; lean_object* v_mctx_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_type_3476_ = lean_ctor_get(v_val_3391_, 3);
v___x_3477_ = lean_st_ref_get(v___y_3373_);
v_mctx_3501_ = lean_ctor_get(v___x_3477_, 0);
lean_inc_ref_n(v_mctx_3501_, 2);
lean_dec(v___x_3477_);
v___x_3502_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v_mctx_3501_);
v___x_3504_ = l_Lean_Expr_hasFVar(v_type_3476_);
if (v___x_3504_ == 0)
{
uint8_t v___x_3505_; 
v___x_3505_ = l_Lean_Expr_hasMVar(v_type_3476_);
if (v___x_3505_ == 0)
{
lean_dec_ref_known(v___x_3503_, 2);
lean_dec_ref(v___f_3397_);
v_fst_3479_ = v___x_3505_;
v_mctx_3480_ = v_mctx_3501_;
goto v___jp_3478_;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v_mctx_3501_);
lean_inc_ref(v_type_3476_);
v___x_3506_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3476_, v___x_3503_);
v___y_3496_ = v___x_3506_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3507_; 
lean_dec_ref(v_mctx_3501_);
lean_inc_ref(v_type_3476_);
v___x_3507_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3397_, v___f_3396_, v_type_3476_, v___x_3503_);
v___y_3496_ = v___x_3507_;
goto v___jp_3495_;
}
v___jp_3478_:
{
lean_object* v___x_3481_; lean_object* v_cache_3482_; lean_object* v_zetaDeltaFVarIds_3483_; lean_object* v_postponed_3484_; lean_object* v_diag_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3493_; 
v___x_3481_ = lean_st_ref_take(v___y_3373_);
v_cache_3482_ = lean_ctor_get(v___x_3481_, 1);
v_zetaDeltaFVarIds_3483_ = lean_ctor_get(v___x_3481_, 2);
v_postponed_3484_ = lean_ctor_get(v___x_3481_, 3);
v_diag_3485_ = lean_ctor_get(v___x_3481_, 4);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v___x_3481_, 0);
lean_dec(v_unused_3494_);
v___x_3487_ = v___x_3481_;
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_diag_3485_);
lean_inc(v_postponed_3484_);
lean_inc(v_zetaDeltaFVarIds_3483_);
lean_inc(v_cache_3482_);
lean_dec(v___x_3481_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_mctx_3480_);
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_mctx_3480_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_cache_3482_);
lean_ctor_set(v_reuseFailAlloc_3492_, 2, v_zetaDeltaFVarIds_3483_);
lean_ctor_set(v_reuseFailAlloc_3492_, 3, v_postponed_3484_);
lean_ctor_set(v_reuseFailAlloc_3492_, 4, v_diag_3485_);
v___x_3490_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_st_ref_put(v___y_3373_, v___x_3490_);
v_a_3393_ = v_fst_3479_;
goto v___jp_3392_;
}
}
}
v___jp_3495_:
{
lean_object* v_snd_3497_; lean_object* v_fst_3498_; lean_object* v_mctx_3499_; uint8_t v___x_3500_; 
v_snd_3497_ = lean_ctor_get(v___y_3496_, 1);
lean_inc(v_snd_3497_);
v_fst_3498_ = lean_ctor_get(v___y_3496_, 0);
lean_inc(v_fst_3498_);
lean_dec_ref(v___y_3496_);
v_mctx_3499_ = lean_ctor_get(v_snd_3497_, 1);
lean_inc_ref(v_mctx_3499_);
lean_dec(v_snd_3497_);
v___x_3500_ = lean_unbox(v_fst_3498_);
lean_dec(v_fst_3498_);
v_fst_3479_ = v___x_3500_;
v_mctx_3480_ = v_mctx_3499_;
goto v___jp_3478_;
}
}
}
v___jp_3392_:
{
if (v_a_3393_ == 0)
{
v_a_3383_ = v_snd_3377_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = l_Lean_LocalDecl_fvarId(v_val_3391_);
v___x_3395_ = lean_array_push(v_snd_3377_, v___x_3394_);
v_a_3383_ = v___x_3395_;
goto v___jp_3382_;
}
}
}
v___jp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_a_3383_);
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3385_ = v___x_3379_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
size_t v___x_3386_; size_t v___x_3387_; 
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3371_, v___x_3386_);
v_i_3371_ = v___x_3387_;
v_b_3372_ = v___x_3385_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3510_, lean_object* v_sz_3511_, lean_object* v_i_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
size_t v_sz_boxed_3516_; size_t v_i_boxed_3517_; lean_object* v_res_3518_; 
v_sz_boxed_3516_ = lean_unbox_usize(v_sz_3511_);
lean_dec(v_sz_3511_);
v_i_boxed_3517_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_res_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3510_, v_sz_boxed_3516_, v_i_boxed_3517_, v_b_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v_as_3510_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3519_, size_t v_sz_3520_, size_t v_i_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_usize_dec_lt(v_i_3521_, v_sz_3520_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_b_3522_);
return v___x_3529_;
}
else
{
lean_object* v_snd_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3661_; 
v_snd_3530_ = lean_ctor_get(v_b_3522_, 1);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_b_3522_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v_b_3522_, 0);
lean_dec(v_unused_3662_);
v___x_3532_ = v_b_3522_;
v_isShared_3533_ = v_isSharedCheck_3661_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_snd_3530_);
lean_dec(v_b_3522_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3661_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v_a_3536_; lean_object* v_a_3543_; 
v___x_3534_ = lean_box(0);
v_a_3543_ = lean_array_uget_borrowed(v_as_3519_, v_i_3521_);
if (lean_obj_tag(v_a_3543_) == 0)
{
v_a_3536_ = v_snd_3530_;
goto v___jp_3535_;
}
else
{
lean_object* v_val_3544_; uint8_t v_a_3546_; lean_object* v___f_3549_; lean_object* v___f_3550_; 
v_val_3544_ = lean_ctor_get(v_a_3543_, 0);
v___f_3549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3530_);
v___f_3550_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3550_, 0, v_snd_3530_);
if (lean_obj_tag(v_val_3544_) == 0)
{
lean_object* v_type_3551_; lean_object* v___x_3552_; uint8_t v_fst_3554_; lean_object* v_mctx_3555_; lean_object* v___y_3571_; lean_object* v_mctx_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_type_3551_ = lean_ctor_get(v_val_3544_, 3);
v___x_3552_ = lean_st_ref_get(v___y_3524_);
v_mctx_3576_ = lean_ctor_get(v___x_3552_, 0);
lean_inc_ref_n(v_mctx_3576_, 2);
lean_dec(v___x_3552_);
v___x_3577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_mctx_3576_);
v___x_3579_ = l_Lean_Expr_hasFVar(v_type_3551_);
if (v___x_3579_ == 0)
{
uint8_t v___x_3580_; 
v___x_3580_ = l_Lean_Expr_hasMVar(v_type_3551_);
if (v___x_3580_ == 0)
{
lean_dec_ref_known(v___x_3578_, 2);
lean_dec_ref(v___f_3550_);
v_fst_3554_ = v___x_3580_;
v_mctx_3555_ = v_mctx_3576_;
goto v___jp_3553_;
}
else
{
lean_object* v___x_3581_; 
lean_dec_ref(v_mctx_3576_);
lean_inc_ref(v_type_3551_);
v___x_3581_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3551_, v___x_3578_);
v___y_3571_ = v___x_3581_;
goto v___jp_3570_;
}
}
else
{
lean_object* v___x_3582_; 
lean_dec_ref(v_mctx_3576_);
lean_inc_ref(v_type_3551_);
v___x_3582_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3551_, v___x_3578_);
v___y_3571_ = v___x_3582_;
goto v___jp_3570_;
}
v___jp_3553_:
{
lean_object* v___x_3556_; lean_object* v_cache_3557_; lean_object* v_zetaDeltaFVarIds_3558_; lean_object* v_postponed_3559_; lean_object* v_diag_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3568_; 
v___x_3556_ = lean_st_ref_take(v___y_3524_);
v_cache_3557_ = lean_ctor_get(v___x_3556_, 1);
v_zetaDeltaFVarIds_3558_ = lean_ctor_get(v___x_3556_, 2);
v_postponed_3559_ = lean_ctor_get(v___x_3556_, 3);
v_diag_3560_ = lean_ctor_get(v___x_3556_, 4);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v___x_3556_, 0);
lean_dec(v_unused_3569_);
v___x_3562_ = v___x_3556_;
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_diag_3560_);
lean_inc(v_postponed_3559_);
lean_inc(v_zetaDeltaFVarIds_3558_);
lean_inc(v_cache_3557_);
lean_dec(v___x_3556_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v_mctx_3555_);
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_mctx_3555_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_cache_3557_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v_zetaDeltaFVarIds_3558_);
lean_ctor_set(v_reuseFailAlloc_3567_, 3, v_postponed_3559_);
lean_ctor_set(v_reuseFailAlloc_3567_, 4, v_diag_3560_);
v___x_3565_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_st_ref_put(v___y_3524_, v___x_3565_);
v_a_3546_ = v_fst_3554_;
goto v___jp_3545_;
}
}
}
v___jp_3570_:
{
lean_object* v_snd_3572_; lean_object* v_fst_3573_; lean_object* v_mctx_3574_; uint8_t v___x_3575_; 
v_snd_3572_ = lean_ctor_get(v___y_3571_, 1);
lean_inc(v_snd_3572_);
v_fst_3573_ = lean_ctor_get(v___y_3571_, 0);
lean_inc(v_fst_3573_);
lean_dec_ref(v___y_3571_);
v_mctx_3574_ = lean_ctor_get(v_snd_3572_, 1);
lean_inc_ref(v_mctx_3574_);
lean_dec(v_snd_3572_);
v___x_3575_ = lean_unbox(v_fst_3573_);
lean_dec(v_fst_3573_);
v_fst_3554_ = v___x_3575_;
v_mctx_3555_ = v_mctx_3574_;
goto v___jp_3553_;
}
}
else
{
uint8_t v_nondep_3583_; 
v_nondep_3583_ = lean_ctor_get_uint8(v_val_3544_, sizeof(void*)*5);
if (v_nondep_3583_ == 0)
{
lean_object* v_type_3584_; lean_object* v_value_3585_; lean_object* v___x_3586_; uint8_t v_fst_3588_; lean_object* v_snd_3589_; lean_object* v___y_3606_; uint8_t v_fst_3611_; lean_object* v_snd_3612_; lean_object* v___y_3618_; lean_object* v_mctx_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_type_3584_ = lean_ctor_get(v_val_3544_, 3);
v_value_3585_ = lean_ctor_get(v_val_3544_, 4);
v___x_3586_ = lean_st_ref_get(v___y_3524_);
v_mctx_3622_ = lean_ctor_get(v___x_3586_, 0);
lean_inc_ref(v_mctx_3622_);
lean_dec(v___x_3586_);
v___x_3623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v_mctx_3622_);
v___x_3625_ = l_Lean_Expr_hasFVar(v_type_3584_);
if (v___x_3625_ == 0)
{
uint8_t v___x_3626_; 
v___x_3626_ = l_Lean_Expr_hasMVar(v_type_3584_);
if (v___x_3626_ == 0)
{
v_fst_3611_ = v___x_3626_;
v_snd_3612_ = v___x_3624_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3627_; 
lean_inc_ref(v_type_3584_);
lean_inc_ref(v___f_3550_);
v___x_3627_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3584_, v___x_3624_);
v___y_3618_ = v___x_3627_;
goto v___jp_3617_;
}
}
else
{
lean_object* v___x_3628_; 
lean_inc_ref(v_type_3584_);
lean_inc_ref(v___f_3550_);
v___x_3628_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3584_, v___x_3624_);
v___y_3618_ = v___x_3628_;
goto v___jp_3617_;
}
v___jp_3587_:
{
lean_object* v_mctx_3590_; lean_object* v___x_3591_; lean_object* v_cache_3592_; lean_object* v_zetaDeltaFVarIds_3593_; lean_object* v_postponed_3594_; lean_object* v_diag_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3603_; 
v_mctx_3590_ = lean_ctor_get(v_snd_3589_, 1);
lean_inc_ref(v_mctx_3590_);
lean_dec_ref(v_snd_3589_);
v___x_3591_ = lean_st_ref_take(v___y_3524_);
v_cache_3592_ = lean_ctor_get(v___x_3591_, 1);
v_zetaDeltaFVarIds_3593_ = lean_ctor_get(v___x_3591_, 2);
v_postponed_3594_ = lean_ctor_get(v___x_3591_, 3);
v_diag_3595_ = lean_ctor_get(v___x_3591_, 4);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3591_, 0);
lean_dec(v_unused_3604_);
v___x_3597_ = v___x_3591_;
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_diag_3595_);
lean_inc(v_postponed_3594_);
lean_inc(v_zetaDeltaFVarIds_3593_);
lean_inc(v_cache_3592_);
lean_dec(v___x_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v_mctx_3590_);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_mctx_3590_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_cache_3592_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_zetaDeltaFVarIds_3593_);
lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_postponed_3594_);
lean_ctor_set(v_reuseFailAlloc_3602_, 4, v_diag_3595_);
v___x_3600_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3601_; 
v___x_3601_ = lean_st_ref_put(v___y_3524_, v___x_3600_);
v_a_3546_ = v_fst_3588_;
goto v___jp_3545_;
}
}
}
v___jp_3605_:
{
lean_object* v_fst_3607_; lean_object* v_snd_3608_; uint8_t v___x_3609_; 
v_fst_3607_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_fst_3607_);
v_snd_3608_ = lean_ctor_get(v___y_3606_, 1);
lean_inc(v_snd_3608_);
lean_dec_ref(v___y_3606_);
v___x_3609_ = lean_unbox(v_fst_3607_);
lean_dec(v_fst_3607_);
v_fst_3588_ = v___x_3609_;
v_snd_3589_ = v_snd_3608_;
goto v___jp_3587_;
}
v___jp_3610_:
{
if (v_fst_3611_ == 0)
{
uint8_t v___x_3613_; 
v___x_3613_ = l_Lean_Expr_hasFVar(v_value_3585_);
if (v___x_3613_ == 0)
{
uint8_t v___x_3614_; 
v___x_3614_ = l_Lean_Expr_hasMVar(v_value_3585_);
if (v___x_3614_ == 0)
{
lean_dec_ref(v___f_3550_);
v_fst_3588_ = v___x_3614_;
v_snd_3589_ = v_snd_3612_;
goto v___jp_3587_;
}
else
{
lean_object* v___x_3615_; 
lean_inc_ref(v_value_3585_);
v___x_3615_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_value_3585_, v_snd_3612_);
v___y_3606_ = v___x_3615_;
goto v___jp_3605_;
}
}
else
{
lean_object* v___x_3616_; 
lean_inc_ref(v_value_3585_);
v___x_3616_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_value_3585_, v_snd_3612_);
v___y_3606_ = v___x_3616_;
goto v___jp_3605_;
}
}
else
{
lean_dec_ref(v___f_3550_);
v_fst_3588_ = v_fst_3611_;
v_snd_3589_ = v_snd_3612_;
goto v___jp_3587_;
}
}
v___jp_3617_:
{
lean_object* v_fst_3619_; lean_object* v_snd_3620_; uint8_t v___x_3621_; 
v_fst_3619_ = lean_ctor_get(v___y_3618_, 0);
lean_inc(v_fst_3619_);
v_snd_3620_ = lean_ctor_get(v___y_3618_, 1);
lean_inc(v_snd_3620_);
lean_dec_ref(v___y_3618_);
v___x_3621_ = lean_unbox(v_fst_3619_);
lean_dec(v_fst_3619_);
v_fst_3611_ = v___x_3621_;
v_snd_3612_ = v_snd_3620_;
goto v___jp_3610_;
}
}
else
{
lean_object* v_type_3629_; lean_object* v___x_3630_; uint8_t v_fst_3632_; lean_object* v_mctx_3633_; lean_object* v___y_3649_; lean_object* v_mctx_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_type_3629_ = lean_ctor_get(v_val_3544_, 3);
v___x_3630_ = lean_st_ref_get(v___y_3524_);
v_mctx_3654_ = lean_ctor_get(v___x_3630_, 0);
lean_inc_ref_n(v_mctx_3654_, 2);
lean_dec(v___x_3630_);
v___x_3655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
lean_ctor_set(v___x_3656_, 1, v_mctx_3654_);
v___x_3657_ = l_Lean_Expr_hasFVar(v_type_3629_);
if (v___x_3657_ == 0)
{
uint8_t v___x_3658_; 
v___x_3658_ = l_Lean_Expr_hasMVar(v_type_3629_);
if (v___x_3658_ == 0)
{
lean_dec_ref_known(v___x_3656_, 2);
lean_dec_ref(v___f_3550_);
v_fst_3632_ = v___x_3658_;
v_mctx_3633_ = v_mctx_3654_;
goto v___jp_3631_;
}
else
{
lean_object* v___x_3659_; 
lean_dec_ref(v_mctx_3654_);
lean_inc_ref(v_type_3629_);
v___x_3659_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3629_, v___x_3656_);
v___y_3649_ = v___x_3659_;
goto v___jp_3648_;
}
}
else
{
lean_object* v___x_3660_; 
lean_dec_ref(v_mctx_3654_);
lean_inc_ref(v_type_3629_);
v___x_3660_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3550_, v___f_3549_, v_type_3629_, v___x_3656_);
v___y_3649_ = v___x_3660_;
goto v___jp_3648_;
}
v___jp_3631_:
{
lean_object* v___x_3634_; lean_object* v_cache_3635_; lean_object* v_zetaDeltaFVarIds_3636_; lean_object* v_postponed_3637_; lean_object* v_diag_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3646_; 
v___x_3634_ = lean_st_ref_take(v___y_3524_);
v_cache_3635_ = lean_ctor_get(v___x_3634_, 1);
v_zetaDeltaFVarIds_3636_ = lean_ctor_get(v___x_3634_, 2);
v_postponed_3637_ = lean_ctor_get(v___x_3634_, 3);
v_diag_3638_ = lean_ctor_get(v___x_3634_, 4);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; 
v_unused_3647_ = lean_ctor_get(v___x_3634_, 0);
lean_dec(v_unused_3647_);
v___x_3640_ = v___x_3634_;
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_diag_3638_);
lean_inc(v_postponed_3637_);
lean_inc(v_zetaDeltaFVarIds_3636_);
lean_inc(v_cache_3635_);
lean_dec(v___x_3634_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v_mctx_3633_);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_mctx_3633_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_cache_3635_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_zetaDeltaFVarIds_3636_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_postponed_3637_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_diag_3638_);
v___x_3643_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_st_ref_put(v___y_3524_, v___x_3643_);
v_a_3546_ = v_fst_3632_;
goto v___jp_3545_;
}
}
}
v___jp_3648_:
{
lean_object* v_snd_3650_; lean_object* v_fst_3651_; lean_object* v_mctx_3652_; uint8_t v___x_3653_; 
v_snd_3650_ = lean_ctor_get(v___y_3649_, 1);
lean_inc(v_snd_3650_);
v_fst_3651_ = lean_ctor_get(v___y_3649_, 0);
lean_inc(v_fst_3651_);
lean_dec_ref(v___y_3649_);
v_mctx_3652_ = lean_ctor_get(v_snd_3650_, 1);
lean_inc_ref(v_mctx_3652_);
lean_dec(v_snd_3650_);
v___x_3653_ = lean_unbox(v_fst_3651_);
lean_dec(v_fst_3651_);
v_fst_3632_ = v___x_3653_;
v_mctx_3633_ = v_mctx_3652_;
goto v___jp_3631_;
}
}
}
v___jp_3545_:
{
if (v_a_3546_ == 0)
{
v_a_3536_ = v_snd_3530_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = l_Lean_LocalDecl_fvarId(v_val_3544_);
v___x_3548_ = lean_array_push(v_snd_3530_, v___x_3547_);
v_a_3536_ = v___x_3548_;
goto v___jp_3535_;
}
}
}
v___jp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 1, v_a_3536_);
lean_ctor_set(v___x_3532_, 0, v___x_3534_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_a_3536_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
size_t v___x_3539_; size_t v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((size_t)1ULL);
v___x_3540_ = lean_usize_add(v_i_3521_, v___x_3539_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3519_, v_sz_3520_, v___x_3540_, v___x_3538_, v___y_3524_);
return v___x_3541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3663_, lean_object* v_sz_3664_, lean_object* v_i_3665_, lean_object* v_b_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
size_t v_sz_boxed_3672_; size_t v_i_boxed_3673_; lean_object* v_res_3674_; 
v_sz_boxed_3672_ = lean_unbox_usize(v_sz_3664_);
lean_dec(v_sz_3664_);
v_i_boxed_3673_ = lean_unbox_usize(v_i_3665_);
lean_dec(v_i_3665_);
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3663_, v_sz_boxed_3672_, v_i_boxed_3673_, v_b_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_as_3663_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3675_, lean_object* v_n_3676_, lean_object* v_b_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
if (lean_obj_tag(v_n_3676_) == 0)
{
lean_object* v_cs_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; size_t v_sz_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v_cs_3683_ = lean_ctor_get(v_n_3676_, 0);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_b_3677_);
v_sz_3686_ = lean_array_size(v_cs_3683_);
v___x_3687_ = ((size_t)0ULL);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3675_, v_cs_3683_, v_sz_3686_, v___x_3687_, v___x_3685_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3703_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3703_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3703_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_fst_3693_; 
v_fst_3693_ = lean_ctor_get(v_a_3689_, 0);
if (lean_obj_tag(v_fst_3693_) == 0)
{
lean_object* v_snd_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
v_snd_3694_ = lean_ctor_get(v_a_3689_, 1);
lean_inc(v_snd_3694_);
lean_dec(v_a_3689_);
v___x_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3695_, 0, v_snd_3694_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3695_);
v___x_3697_ = v___x_3691_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
else
{
lean_object* v_val_3699_; lean_object* v___x_3701_; 
lean_inc_ref(v_fst_3693_);
lean_dec(v_a_3689_);
v_val_3699_ = lean_ctor_get(v_fst_3693_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v_fst_3693_, 1);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v_val_3699_);
v___x_3701_ = v___x_3691_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_val_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
v_a_3704_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3688_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3688_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
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
lean_object* v_vs_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; size_t v_sz_3715_; size_t v___x_3716_; lean_object* v___x_3717_; 
v_vs_3712_ = lean_ctor_get(v_n_3676_, 0);
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v_b_3677_);
v_sz_3715_ = lean_array_size(v_vs_3712_);
v___x_3716_ = ((size_t)0ULL);
v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3712_, v_sz_3715_, v___x_3716_, v___x_3714_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3732_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_fst_3722_; 
v_fst_3722_ = lean_ctor_get(v_a_3718_, 0);
if (lean_obj_tag(v_fst_3722_) == 0)
{
lean_object* v_snd_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v_snd_3723_ = lean_ctor_get(v_a_3718_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_a_3718_);
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_snd_3723_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3724_);
v___x_3726_ = v___x_3720_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3730_; 
lean_inc_ref(v_fst_3722_);
lean_dec(v_a_3718_);
v_val_3728_ = lean_ctor_get(v_fst_3722_, 0);
lean_inc(v_val_3728_);
lean_dec_ref_known(v_fst_3722_, 1);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_val_3728_);
v___x_3730_ = v___x_3720_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_val_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v_a_3733_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3717_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3717_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3741_, lean_object* v_as_3742_, size_t v_sz_3743_, size_t v_i_3744_, lean_object* v_b_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_usize_dec_lt(v_i_3744_, v_sz_3743_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_b_3745_);
return v___x_3752_;
}
else
{
lean_object* v_snd_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3787_; 
v_snd_3753_ = lean_ctor_get(v_b_3745_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_b_3745_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v_b_3745_, 0);
lean_dec(v_unused_3788_);
v___x_3755_ = v_b_3745_;
v_isShared_3756_ = v_isSharedCheck_3787_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_snd_3753_);
lean_dec(v_b_3745_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3787_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_a_3757_; lean_object* v___x_3758_; 
v_a_3757_ = lean_array_uget_borrowed(v_as_3742_, v_i_3744_);
lean_inc(v_snd_3753_);
v___x_3758_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3741_, v_a_3757_, v_snd_3753_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3778_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3778_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3778_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
if (lean_obj_tag(v_a_3759_) == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3759_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3763_);
v___x_3765_ = v___x_3755_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_snd_3753_);
v___x_3765_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3767_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3765_);
v___x_3767_ = v___x_3761_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
lean_del_object(v___x_3761_);
lean_dec(v_snd_3753_);
v_a_3770_ = lean_ctor_get(v_a_3759_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v_a_3759_, 1);
v___x_3771_ = lean_box(0);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v_a_3770_);
lean_ctor_set(v___x_3755_, 0, v___x_3771_);
v___x_3773_ = v___x_3755_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_a_3770_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
size_t v___x_3774_; size_t v___x_3775_; 
v___x_3774_ = ((size_t)1ULL);
v___x_3775_ = lean_usize_add(v_i_3744_, v___x_3774_);
v_i_3744_ = v___x_3775_;
v_b_3745_ = v___x_3773_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_del_object(v___x_3755_);
lean_dec(v_snd_3753_);
v_a_3779_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3758_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3758_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3789_, lean_object* v_as_3790_, lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
size_t v_sz_boxed_3799_; size_t v_i_boxed_3800_; lean_object* v_res_3801_; 
v_sz_boxed_3799_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3800_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3789_, v_as_3790_, v_sz_boxed_3799_, v_i_boxed_3800_, v_b_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3790_);
lean_dec_ref(v_init_3789_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3802_, lean_object* v_n_3803_, lean_object* v_b_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3802_, v_n_3803_, v_b_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v_n_3803_);
lean_dec_ref(v_init_3802_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3811_, size_t v_sz_3812_, size_t v_i_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_){
_start:
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3818_, 0, v_b_3814_);
return v___x_3818_;
}
else
{
lean_object* v_snd_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3950_; 
v_snd_3819_ = lean_ctor_get(v_b_3814_, 1);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_b_3814_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v_b_3814_, 0);
lean_dec(v_unused_3951_);
v___x_3821_ = v_b_3814_;
v_isShared_3822_ = v_isSharedCheck_3950_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_snd_3819_);
lean_dec(v_b_3814_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3950_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v_a_3825_; lean_object* v_a_3832_; 
v___x_3823_ = lean_box(0);
v_a_3832_ = lean_array_uget_borrowed(v_as_3811_, v_i_3813_);
if (lean_obj_tag(v_a_3832_) == 0)
{
v_a_3825_ = v_snd_3819_;
goto v___jp_3824_;
}
else
{
lean_object* v_val_3833_; uint8_t v_a_3835_; lean_object* v___f_3838_; lean_object* v___f_3839_; 
v_val_3833_ = lean_ctor_get(v_a_3832_, 0);
v___f_3838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3819_);
v___f_3839_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3839_, 0, v_snd_3819_);
if (lean_obj_tag(v_val_3833_) == 0)
{
lean_object* v_type_3840_; lean_object* v___x_3841_; uint8_t v_fst_3843_; lean_object* v_mctx_3844_; lean_object* v___y_3860_; lean_object* v_mctx_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v_type_3840_ = lean_ctor_get(v_val_3833_, 3);
v___x_3841_ = lean_st_ref_get(v___y_3815_);
v_mctx_3865_ = lean_ctor_get(v___x_3841_, 0);
lean_inc_ref_n(v_mctx_3865_, 2);
lean_dec(v___x_3841_);
v___x_3866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v_mctx_3865_);
v___x_3868_ = l_Lean_Expr_hasFVar(v_type_3840_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_Expr_hasMVar(v_type_3840_);
if (v___x_3869_ == 0)
{
lean_dec_ref_known(v___x_3867_, 2);
lean_dec_ref(v___f_3839_);
v_fst_3843_ = v___x_3869_;
v_mctx_3844_ = v_mctx_3865_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3870_; 
lean_dec_ref(v_mctx_3865_);
lean_inc_ref(v_type_3840_);
v___x_3870_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3840_, v___x_3867_);
v___y_3860_ = v___x_3870_;
goto v___jp_3859_;
}
}
else
{
lean_object* v___x_3871_; 
lean_dec_ref(v_mctx_3865_);
lean_inc_ref(v_type_3840_);
v___x_3871_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3840_, v___x_3867_);
v___y_3860_ = v___x_3871_;
goto v___jp_3859_;
}
v___jp_3842_:
{
lean_object* v___x_3845_; lean_object* v_cache_3846_; lean_object* v_zetaDeltaFVarIds_3847_; lean_object* v_postponed_3848_; lean_object* v_diag_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3857_; 
v___x_3845_ = lean_st_ref_take(v___y_3815_);
v_cache_3846_ = lean_ctor_get(v___x_3845_, 1);
v_zetaDeltaFVarIds_3847_ = lean_ctor_get(v___x_3845_, 2);
v_postponed_3848_ = lean_ctor_get(v___x_3845_, 3);
v_diag_3849_ = lean_ctor_get(v___x_3845_, 4);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v___x_3845_, 0);
lean_dec(v_unused_3858_);
v___x_3851_ = v___x_3845_;
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_diag_3849_);
lean_inc(v_postponed_3848_);
lean_inc(v_zetaDeltaFVarIds_3847_);
lean_inc(v_cache_3846_);
lean_dec(v___x_3845_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3857_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v_mctx_3844_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_mctx_3844_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_cache_3846_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_zetaDeltaFVarIds_3847_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_postponed_3848_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_diag_3849_);
v___x_3854_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_st_ref_put(v___y_3815_, v___x_3854_);
v_a_3835_ = v_fst_3843_;
goto v___jp_3834_;
}
}
}
v___jp_3859_:
{
lean_object* v_snd_3861_; lean_object* v_fst_3862_; lean_object* v_mctx_3863_; uint8_t v___x_3864_; 
v_snd_3861_ = lean_ctor_get(v___y_3860_, 1);
lean_inc(v_snd_3861_);
v_fst_3862_ = lean_ctor_get(v___y_3860_, 0);
lean_inc(v_fst_3862_);
lean_dec_ref(v___y_3860_);
v_mctx_3863_ = lean_ctor_get(v_snd_3861_, 1);
lean_inc_ref(v_mctx_3863_);
lean_dec(v_snd_3861_);
v___x_3864_ = lean_unbox(v_fst_3862_);
lean_dec(v_fst_3862_);
v_fst_3843_ = v___x_3864_;
v_mctx_3844_ = v_mctx_3863_;
goto v___jp_3842_;
}
}
else
{
uint8_t v_nondep_3872_; 
v_nondep_3872_ = lean_ctor_get_uint8(v_val_3833_, sizeof(void*)*5);
if (v_nondep_3872_ == 0)
{
lean_object* v_type_3873_; lean_object* v_value_3874_; lean_object* v___x_3875_; uint8_t v_fst_3877_; lean_object* v_snd_3878_; lean_object* v___y_3895_; uint8_t v_fst_3900_; lean_object* v_snd_3901_; lean_object* v___y_3907_; lean_object* v_mctx_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_type_3873_ = lean_ctor_get(v_val_3833_, 3);
v_value_3874_ = lean_ctor_get(v_val_3833_, 4);
v___x_3875_ = lean_st_ref_get(v___y_3815_);
v_mctx_3911_ = lean_ctor_get(v___x_3875_, 0);
lean_inc_ref(v_mctx_3911_);
lean_dec(v___x_3875_);
v___x_3912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v_mctx_3911_);
v___x_3914_ = l_Lean_Expr_hasFVar(v_type_3873_);
if (v___x_3914_ == 0)
{
uint8_t v___x_3915_; 
v___x_3915_ = l_Lean_Expr_hasMVar(v_type_3873_);
if (v___x_3915_ == 0)
{
v_fst_3900_ = v___x_3915_;
v_snd_3901_ = v___x_3913_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3916_; 
lean_inc_ref(v_type_3873_);
lean_inc_ref(v___f_3839_);
v___x_3916_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3873_, v___x_3913_);
v___y_3907_ = v___x_3916_;
goto v___jp_3906_;
}
}
else
{
lean_object* v___x_3917_; 
lean_inc_ref(v_type_3873_);
lean_inc_ref(v___f_3839_);
v___x_3917_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3873_, v___x_3913_);
v___y_3907_ = v___x_3917_;
goto v___jp_3906_;
}
v___jp_3876_:
{
lean_object* v_mctx_3879_; lean_object* v___x_3880_; lean_object* v_cache_3881_; lean_object* v_zetaDeltaFVarIds_3882_; lean_object* v_postponed_3883_; lean_object* v_diag_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3892_; 
v_mctx_3879_ = lean_ctor_get(v_snd_3878_, 1);
lean_inc_ref(v_mctx_3879_);
lean_dec_ref(v_snd_3878_);
v___x_3880_ = lean_st_ref_take(v___y_3815_);
v_cache_3881_ = lean_ctor_get(v___x_3880_, 1);
v_zetaDeltaFVarIds_3882_ = lean_ctor_get(v___x_3880_, 2);
v_postponed_3883_ = lean_ctor_get(v___x_3880_, 3);
v_diag_3884_ = lean_ctor_get(v___x_3880_, 4);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; 
v_unused_3893_ = lean_ctor_get(v___x_3880_, 0);
lean_dec(v_unused_3893_);
v___x_3886_ = v___x_3880_;
v_isShared_3887_ = v_isSharedCheck_3892_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_diag_3884_);
lean_inc(v_postponed_3883_);
lean_inc(v_zetaDeltaFVarIds_3882_);
lean_inc(v_cache_3881_);
lean_dec(v___x_3880_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3892_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v_mctx_3879_);
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_mctx_3879_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_cache_3881_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_zetaDeltaFVarIds_3882_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_postponed_3883_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v_diag_3884_);
v___x_3889_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_st_ref_put(v___y_3815_, v___x_3889_);
v_a_3835_ = v_fst_3877_;
goto v___jp_3834_;
}
}
}
v___jp_3894_:
{
lean_object* v_fst_3896_; lean_object* v_snd_3897_; uint8_t v___x_3898_; 
v_fst_3896_ = lean_ctor_get(v___y_3895_, 0);
lean_inc(v_fst_3896_);
v_snd_3897_ = lean_ctor_get(v___y_3895_, 1);
lean_inc(v_snd_3897_);
lean_dec_ref(v___y_3895_);
v___x_3898_ = lean_unbox(v_fst_3896_);
lean_dec(v_fst_3896_);
v_fst_3877_ = v___x_3898_;
v_snd_3878_ = v_snd_3897_;
goto v___jp_3876_;
}
v___jp_3899_:
{
if (v_fst_3900_ == 0)
{
uint8_t v___x_3902_; 
v___x_3902_ = l_Lean_Expr_hasFVar(v_value_3874_);
if (v___x_3902_ == 0)
{
uint8_t v___x_3903_; 
v___x_3903_ = l_Lean_Expr_hasMVar(v_value_3874_);
if (v___x_3903_ == 0)
{
lean_dec_ref(v___f_3839_);
v_fst_3877_ = v___x_3903_;
v_snd_3878_ = v_snd_3901_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3904_; 
lean_inc_ref(v_value_3874_);
v___x_3904_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_value_3874_, v_snd_3901_);
v___y_3895_ = v___x_3904_;
goto v___jp_3894_;
}
}
else
{
lean_object* v___x_3905_; 
lean_inc_ref(v_value_3874_);
v___x_3905_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_value_3874_, v_snd_3901_);
v___y_3895_ = v___x_3905_;
goto v___jp_3894_;
}
}
else
{
lean_dec_ref(v___f_3839_);
v_fst_3877_ = v_fst_3900_;
v_snd_3878_ = v_snd_3901_;
goto v___jp_3876_;
}
}
v___jp_3906_:
{
lean_object* v_fst_3908_; lean_object* v_snd_3909_; uint8_t v___x_3910_; 
v_fst_3908_ = lean_ctor_get(v___y_3907_, 0);
lean_inc(v_fst_3908_);
v_snd_3909_ = lean_ctor_get(v___y_3907_, 1);
lean_inc(v_snd_3909_);
lean_dec_ref(v___y_3907_);
v___x_3910_ = lean_unbox(v_fst_3908_);
lean_dec(v_fst_3908_);
v_fst_3900_ = v___x_3910_;
v_snd_3901_ = v_snd_3909_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_type_3918_; lean_object* v___x_3919_; uint8_t v_fst_3921_; lean_object* v_mctx_3922_; lean_object* v___y_3938_; lean_object* v_mctx_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v_type_3918_ = lean_ctor_get(v_val_3833_, 3);
v___x_3919_ = lean_st_ref_get(v___y_3815_);
v_mctx_3943_ = lean_ctor_get(v___x_3919_, 0);
lean_inc_ref_n(v_mctx_3943_, 2);
lean_dec(v___x_3919_);
v___x_3944_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v_mctx_3943_);
v___x_3946_ = l_Lean_Expr_hasFVar(v_type_3918_);
if (v___x_3946_ == 0)
{
uint8_t v___x_3947_; 
v___x_3947_ = l_Lean_Expr_hasMVar(v_type_3918_);
if (v___x_3947_ == 0)
{
lean_dec_ref_known(v___x_3945_, 2);
lean_dec_ref(v___f_3839_);
v_fst_3921_ = v___x_3947_;
v_mctx_3922_ = v_mctx_3943_;
goto v___jp_3920_;
}
else
{
lean_object* v___x_3948_; 
lean_dec_ref(v_mctx_3943_);
lean_inc_ref(v_type_3918_);
v___x_3948_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3918_, v___x_3945_);
v___y_3938_ = v___x_3948_;
goto v___jp_3937_;
}
}
else
{
lean_object* v___x_3949_; 
lean_dec_ref(v_mctx_3943_);
lean_inc_ref(v_type_3918_);
v___x_3949_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3839_, v___f_3838_, v_type_3918_, v___x_3945_);
v___y_3938_ = v___x_3949_;
goto v___jp_3937_;
}
v___jp_3920_:
{
lean_object* v___x_3923_; lean_object* v_cache_3924_; lean_object* v_zetaDeltaFVarIds_3925_; lean_object* v_postponed_3926_; lean_object* v_diag_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3935_; 
v___x_3923_ = lean_st_ref_take(v___y_3815_);
v_cache_3924_ = lean_ctor_get(v___x_3923_, 1);
v_zetaDeltaFVarIds_3925_ = lean_ctor_get(v___x_3923_, 2);
v_postponed_3926_ = lean_ctor_get(v___x_3923_, 3);
v_diag_3927_ = lean_ctor_get(v___x_3923_, 4);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v___x_3923_, 0);
lean_dec(v_unused_3936_);
v___x_3929_ = v___x_3923_;
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_diag_3927_);
lean_inc(v_postponed_3926_);
lean_inc(v_zetaDeltaFVarIds_3925_);
lean_inc(v_cache_3924_);
lean_dec(v___x_3923_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v_mctx_3922_);
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_mctx_3922_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_cache_3924_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_zetaDeltaFVarIds_3925_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_postponed_3926_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_diag_3927_);
v___x_3932_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_st_ref_put(v___y_3815_, v___x_3932_);
v_a_3835_ = v_fst_3921_;
goto v___jp_3834_;
}
}
}
v___jp_3937_:
{
lean_object* v_snd_3939_; lean_object* v_fst_3940_; lean_object* v_mctx_3941_; uint8_t v___x_3942_; 
v_snd_3939_ = lean_ctor_get(v___y_3938_, 1);
lean_inc(v_snd_3939_);
v_fst_3940_ = lean_ctor_get(v___y_3938_, 0);
lean_inc(v_fst_3940_);
lean_dec_ref(v___y_3938_);
v_mctx_3941_ = lean_ctor_get(v_snd_3939_, 1);
lean_inc_ref(v_mctx_3941_);
lean_dec(v_snd_3939_);
v___x_3942_ = lean_unbox(v_fst_3940_);
lean_dec(v_fst_3940_);
v_fst_3921_ = v___x_3942_;
v_mctx_3922_ = v_mctx_3941_;
goto v___jp_3920_;
}
}
}
v___jp_3834_:
{
if (v_a_3835_ == 0)
{
v_a_3825_ = v_snd_3819_;
goto v___jp_3824_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = l_Lean_LocalDecl_fvarId(v_val_3833_);
v___x_3837_ = lean_array_push(v_snd_3819_, v___x_3836_);
v_a_3825_ = v___x_3837_;
goto v___jp_3824_;
}
}
}
v___jp_3824_:
{
lean_object* v___x_3827_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v_a_3825_);
lean_ctor_set(v___x_3821_, 0, v___x_3823_);
v___x_3827_ = v___x_3821_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_a_3825_);
v___x_3827_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
size_t v___x_3828_; size_t v___x_3829_; 
v___x_3828_ = ((size_t)1ULL);
v___x_3829_ = lean_usize_add(v_i_3813_, v___x_3828_);
v_i_3813_ = v___x_3829_;
v_b_3814_ = v___x_3827_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3952_, lean_object* v_sz_3953_, lean_object* v_i_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
size_t v_sz_boxed_3958_; size_t v_i_boxed_3959_; lean_object* v_res_3960_; 
v_sz_boxed_3958_ = lean_unbox_usize(v_sz_3953_);
lean_dec(v_sz_3953_);
v_i_boxed_3959_ = lean_unbox_usize(v_i_3954_);
lean_dec(v_i_3954_);
v_res_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3952_, v_sz_boxed_3958_, v_i_boxed_3959_, v_b_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v_as_3952_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3961_, size_t v_sz_3962_, size_t v_i_3963_, lean_object* v_b_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
uint8_t v___x_3970_; 
v___x_3970_ = lean_usize_dec_lt(v_i_3963_, v_sz_3962_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_b_3964_);
return v___x_3971_;
}
else
{
lean_object* v_snd_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4103_; 
v_snd_3972_ = lean_ctor_get(v_b_3964_, 1);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_b_3964_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; 
v_unused_4104_ = lean_ctor_get(v_b_3964_, 0);
lean_dec(v_unused_4104_);
v___x_3974_ = v_b_3964_;
v_isShared_3975_ = v_isSharedCheck_4103_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_snd_3972_);
lean_dec(v_b_3964_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4103_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v_a_3978_; lean_object* v_a_3985_; 
v___x_3976_ = lean_box(0);
v_a_3985_ = lean_array_uget_borrowed(v_as_3961_, v_i_3963_);
if (lean_obj_tag(v_a_3985_) == 0)
{
v_a_3978_ = v_snd_3972_;
goto v___jp_3977_;
}
else
{
lean_object* v_val_3986_; uint8_t v_a_3988_; lean_object* v___f_3991_; lean_object* v___f_3992_; 
v_val_3986_ = lean_ctor_get(v_a_3985_, 0);
v___f_3991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3972_);
v___f_3992_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3992_, 0, v_snd_3972_);
if (lean_obj_tag(v_val_3986_) == 0)
{
lean_object* v_type_3993_; lean_object* v___x_3994_; uint8_t v_fst_3996_; lean_object* v_mctx_3997_; lean_object* v___y_4013_; lean_object* v_mctx_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v_type_3993_ = lean_ctor_get(v_val_3986_, 3);
v___x_3994_ = lean_st_ref_get(v___y_3966_);
v_mctx_4018_ = lean_ctor_get(v___x_3994_, 0);
lean_inc_ref_n(v_mctx_4018_, 2);
lean_dec(v___x_3994_);
v___x_4019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
lean_ctor_set(v___x_4020_, 1, v_mctx_4018_);
v___x_4021_ = l_Lean_Expr_hasFVar(v_type_3993_);
if (v___x_4021_ == 0)
{
uint8_t v___x_4022_; 
v___x_4022_ = l_Lean_Expr_hasMVar(v_type_3993_);
if (v___x_4022_ == 0)
{
lean_dec_ref_known(v___x_4020_, 2);
lean_dec_ref(v___f_3992_);
v_fst_3996_ = v___x_4022_;
v_mctx_3997_ = v_mctx_4018_;
goto v___jp_3995_;
}
else
{
lean_object* v___x_4023_; 
lean_dec_ref(v_mctx_4018_);
lean_inc_ref(v_type_3993_);
v___x_4023_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_3993_, v___x_4020_);
v___y_4013_ = v___x_4023_;
goto v___jp_4012_;
}
}
else
{
lean_object* v___x_4024_; 
lean_dec_ref(v_mctx_4018_);
lean_inc_ref(v_type_3993_);
v___x_4024_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_3993_, v___x_4020_);
v___y_4013_ = v___x_4024_;
goto v___jp_4012_;
}
v___jp_3995_:
{
lean_object* v___x_3998_; lean_object* v_cache_3999_; lean_object* v_zetaDeltaFVarIds_4000_; lean_object* v_postponed_4001_; lean_object* v_diag_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
v___x_3998_ = lean_st_ref_take(v___y_3966_);
v_cache_3999_ = lean_ctor_get(v___x_3998_, 1);
v_zetaDeltaFVarIds_4000_ = lean_ctor_get(v___x_3998_, 2);
v_postponed_4001_ = lean_ctor_get(v___x_3998_, 3);
v_diag_4002_ = lean_ctor_get(v___x_3998_, 4);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; 
v_unused_4011_ = lean_ctor_get(v___x_3998_, 0);
lean_dec(v_unused_4011_);
v___x_4004_ = v___x_3998_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_diag_4002_);
lean_inc(v_postponed_4001_);
lean_inc(v_zetaDeltaFVarIds_4000_);
lean_inc(v_cache_3999_);
lean_dec(v___x_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v_mctx_3997_);
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_mctx_3997_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_cache_3999_);
lean_ctor_set(v_reuseFailAlloc_4009_, 2, v_zetaDeltaFVarIds_4000_);
lean_ctor_set(v_reuseFailAlloc_4009_, 3, v_postponed_4001_);
lean_ctor_set(v_reuseFailAlloc_4009_, 4, v_diag_4002_);
v___x_4007_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_st_ref_put(v___y_3966_, v___x_4007_);
v_a_3988_ = v_fst_3996_;
goto v___jp_3987_;
}
}
}
v___jp_4012_:
{
lean_object* v_snd_4014_; lean_object* v_fst_4015_; lean_object* v_mctx_4016_; uint8_t v___x_4017_; 
v_snd_4014_ = lean_ctor_get(v___y_4013_, 1);
lean_inc(v_snd_4014_);
v_fst_4015_ = lean_ctor_get(v___y_4013_, 0);
lean_inc(v_fst_4015_);
lean_dec_ref(v___y_4013_);
v_mctx_4016_ = lean_ctor_get(v_snd_4014_, 1);
lean_inc_ref(v_mctx_4016_);
lean_dec(v_snd_4014_);
v___x_4017_ = lean_unbox(v_fst_4015_);
lean_dec(v_fst_4015_);
v_fst_3996_ = v___x_4017_;
v_mctx_3997_ = v_mctx_4016_;
goto v___jp_3995_;
}
}
else
{
uint8_t v_nondep_4025_; 
v_nondep_4025_ = lean_ctor_get_uint8(v_val_3986_, sizeof(void*)*5);
if (v_nondep_4025_ == 0)
{
lean_object* v_type_4026_; lean_object* v_value_4027_; lean_object* v___x_4028_; uint8_t v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___y_4048_; uint8_t v_fst_4053_; lean_object* v_snd_4054_; lean_object* v___y_4060_; lean_object* v_mctx_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v_type_4026_ = lean_ctor_get(v_val_3986_, 3);
v_value_4027_ = lean_ctor_get(v_val_3986_, 4);
v___x_4028_ = lean_st_ref_get(v___y_3966_);
v_mctx_4064_ = lean_ctor_get(v___x_4028_, 0);
lean_inc_ref(v_mctx_4064_);
lean_dec(v___x_4028_);
v___x_4065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
lean_ctor_set(v___x_4066_, 1, v_mctx_4064_);
v___x_4067_ = l_Lean_Expr_hasFVar(v_type_4026_);
if (v___x_4067_ == 0)
{
uint8_t v___x_4068_; 
v___x_4068_ = l_Lean_Expr_hasMVar(v_type_4026_);
if (v___x_4068_ == 0)
{
v_fst_4053_ = v___x_4068_;
v_snd_4054_ = v___x_4066_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4069_; 
lean_inc_ref(v_type_4026_);
lean_inc_ref(v___f_3992_);
v___x_4069_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_4026_, v___x_4066_);
v___y_4060_ = v___x_4069_;
goto v___jp_4059_;
}
}
else
{
lean_object* v___x_4070_; 
lean_inc_ref(v_type_4026_);
lean_inc_ref(v___f_3992_);
v___x_4070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_4026_, v___x_4066_);
v___y_4060_ = v___x_4070_;
goto v___jp_4059_;
}
v___jp_4029_:
{
lean_object* v_mctx_4032_; lean_object* v___x_4033_; lean_object* v_cache_4034_; lean_object* v_zetaDeltaFVarIds_4035_; lean_object* v_postponed_4036_; lean_object* v_diag_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4045_; 
v_mctx_4032_ = lean_ctor_get(v_snd_4031_, 1);
lean_inc_ref(v_mctx_4032_);
lean_dec_ref(v_snd_4031_);
v___x_4033_ = lean_st_ref_take(v___y_3966_);
v_cache_4034_ = lean_ctor_get(v___x_4033_, 1);
v_zetaDeltaFVarIds_4035_ = lean_ctor_get(v___x_4033_, 2);
v_postponed_4036_ = lean_ctor_get(v___x_4033_, 3);
v_diag_4037_ = lean_ctor_get(v___x_4033_, 4);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v___x_4033_, 0);
lean_dec(v_unused_4046_);
v___x_4039_ = v___x_4033_;
v_isShared_4040_ = v_isSharedCheck_4045_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_diag_4037_);
lean_inc(v_postponed_4036_);
lean_inc(v_zetaDeltaFVarIds_4035_);
lean_inc(v_cache_4034_);
lean_dec(v___x_4033_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4045_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v_mctx_4032_);
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_mctx_4032_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_cache_4034_);
lean_ctor_set(v_reuseFailAlloc_4044_, 2, v_zetaDeltaFVarIds_4035_);
lean_ctor_set(v_reuseFailAlloc_4044_, 3, v_postponed_4036_);
lean_ctor_set(v_reuseFailAlloc_4044_, 4, v_diag_4037_);
v___x_4042_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4043_; 
v___x_4043_ = lean_st_ref_put(v___y_3966_, v___x_4042_);
v_a_3988_ = v_fst_4030_;
goto v___jp_3987_;
}
}
}
v___jp_4047_:
{
lean_object* v_fst_4049_; lean_object* v_snd_4050_; uint8_t v___x_4051_; 
v_fst_4049_ = lean_ctor_get(v___y_4048_, 0);
lean_inc(v_fst_4049_);
v_snd_4050_ = lean_ctor_get(v___y_4048_, 1);
lean_inc(v_snd_4050_);
lean_dec_ref(v___y_4048_);
v___x_4051_ = lean_unbox(v_fst_4049_);
lean_dec(v_fst_4049_);
v_fst_4030_ = v___x_4051_;
v_snd_4031_ = v_snd_4050_;
goto v___jp_4029_;
}
v___jp_4052_:
{
if (v_fst_4053_ == 0)
{
uint8_t v___x_4055_; 
v___x_4055_ = l_Lean_Expr_hasFVar(v_value_4027_);
if (v___x_4055_ == 0)
{
uint8_t v___x_4056_; 
v___x_4056_ = l_Lean_Expr_hasMVar(v_value_4027_);
if (v___x_4056_ == 0)
{
lean_dec_ref(v___f_3992_);
v_fst_4030_ = v___x_4056_;
v_snd_4031_ = v_snd_4054_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4057_; 
lean_inc_ref(v_value_4027_);
v___x_4057_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_value_4027_, v_snd_4054_);
v___y_4048_ = v___x_4057_;
goto v___jp_4047_;
}
}
else
{
lean_object* v___x_4058_; 
lean_inc_ref(v_value_4027_);
v___x_4058_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_value_4027_, v_snd_4054_);
v___y_4048_ = v___x_4058_;
goto v___jp_4047_;
}
}
else
{
lean_dec_ref(v___f_3992_);
v_fst_4030_ = v_fst_4053_;
v_snd_4031_ = v_snd_4054_;
goto v___jp_4029_;
}
}
v___jp_4059_:
{
lean_object* v_fst_4061_; lean_object* v_snd_4062_; uint8_t v___x_4063_; 
v_fst_4061_ = lean_ctor_get(v___y_4060_, 0);
lean_inc(v_fst_4061_);
v_snd_4062_ = lean_ctor_get(v___y_4060_, 1);
lean_inc(v_snd_4062_);
lean_dec_ref(v___y_4060_);
v___x_4063_ = lean_unbox(v_fst_4061_);
lean_dec(v_fst_4061_);
v_fst_4053_ = v___x_4063_;
v_snd_4054_ = v_snd_4062_;
goto v___jp_4052_;
}
}
else
{
lean_object* v_type_4071_; lean_object* v___x_4072_; uint8_t v_fst_4074_; lean_object* v_mctx_4075_; lean_object* v___y_4091_; lean_object* v_mctx_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_type_4071_ = lean_ctor_get(v_val_3986_, 3);
v___x_4072_ = lean_st_ref_get(v___y_3966_);
v_mctx_4096_ = lean_ctor_get(v___x_4072_, 0);
lean_inc_ref_n(v_mctx_4096_, 2);
lean_dec(v___x_4072_);
v___x_4097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v_mctx_4096_);
v___x_4099_ = l_Lean_Expr_hasFVar(v_type_4071_);
if (v___x_4099_ == 0)
{
uint8_t v___x_4100_; 
v___x_4100_ = l_Lean_Expr_hasMVar(v_type_4071_);
if (v___x_4100_ == 0)
{
lean_dec_ref_known(v___x_4098_, 2);
lean_dec_ref(v___f_3992_);
v_fst_4074_ = v___x_4100_;
v_mctx_4075_ = v_mctx_4096_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4101_; 
lean_dec_ref(v_mctx_4096_);
lean_inc_ref(v_type_4071_);
v___x_4101_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_4071_, v___x_4098_);
v___y_4091_ = v___x_4101_;
goto v___jp_4090_;
}
}
else
{
lean_object* v___x_4102_; 
lean_dec_ref(v_mctx_4096_);
lean_inc_ref(v_type_4071_);
v___x_4102_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3992_, v___f_3991_, v_type_4071_, v___x_4098_);
v___y_4091_ = v___x_4102_;
goto v___jp_4090_;
}
v___jp_4073_:
{
lean_object* v___x_4076_; lean_object* v_cache_4077_; lean_object* v_zetaDeltaFVarIds_4078_; lean_object* v_postponed_4079_; lean_object* v_diag_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4088_; 
v___x_4076_ = lean_st_ref_take(v___y_3966_);
v_cache_4077_ = lean_ctor_get(v___x_4076_, 1);
v_zetaDeltaFVarIds_4078_ = lean_ctor_get(v___x_4076_, 2);
v_postponed_4079_ = lean_ctor_get(v___x_4076_, 3);
v_diag_4080_ = lean_ctor_get(v___x_4076_, 4);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v___x_4076_, 0);
lean_dec(v_unused_4089_);
v___x_4082_ = v___x_4076_;
v_isShared_4083_ = v_isSharedCheck_4088_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_diag_4080_);
lean_inc(v_postponed_4079_);
lean_inc(v_zetaDeltaFVarIds_4078_);
lean_inc(v_cache_4077_);
lean_dec(v___x_4076_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4088_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v_mctx_4075_);
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_mctx_4075_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_cache_4077_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_zetaDeltaFVarIds_4078_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_postponed_4079_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_diag_4080_);
v___x_4085_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_st_ref_put(v___y_3966_, v___x_4085_);
v_a_3988_ = v_fst_4074_;
goto v___jp_3987_;
}
}
}
v___jp_4090_:
{
lean_object* v_snd_4092_; lean_object* v_fst_4093_; lean_object* v_mctx_4094_; uint8_t v___x_4095_; 
v_snd_4092_ = lean_ctor_get(v___y_4091_, 1);
lean_inc(v_snd_4092_);
v_fst_4093_ = lean_ctor_get(v___y_4091_, 0);
lean_inc(v_fst_4093_);
lean_dec_ref(v___y_4091_);
v_mctx_4094_ = lean_ctor_get(v_snd_4092_, 1);
lean_inc_ref(v_mctx_4094_);
lean_dec(v_snd_4092_);
v___x_4095_ = lean_unbox(v_fst_4093_);
lean_dec(v_fst_4093_);
v_fst_4074_ = v___x_4095_;
v_mctx_4075_ = v_mctx_4094_;
goto v___jp_4073_;
}
}
}
v___jp_3987_:
{
if (v_a_3988_ == 0)
{
v_a_3978_ = v_snd_3972_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = l_Lean_LocalDecl_fvarId(v_val_3986_);
v___x_3990_ = lean_array_push(v_snd_3972_, v___x_3989_);
v_a_3978_ = v___x_3990_;
goto v___jp_3977_;
}
}
}
v___jp_3977_:
{
lean_object* v___x_3980_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v_a_3978_);
lean_ctor_set(v___x_3974_, 0, v___x_3976_);
v___x_3980_ = v___x_3974_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_a_3978_);
v___x_3980_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
size_t v___x_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_add(v_i_3963_, v___x_3981_);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3961_, v_sz_3962_, v___x_3982_, v___x_3980_, v___y_3966_);
return v___x_3983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4105_, lean_object* v_sz_4106_, lean_object* v_i_4107_, lean_object* v_b_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
size_t v_sz_boxed_4114_; size_t v_i_boxed_4115_; lean_object* v_res_4116_; 
v_sz_boxed_4114_ = lean_unbox_usize(v_sz_4106_);
lean_dec(v_sz_4106_);
v_i_boxed_4115_ = lean_unbox_usize(v_i_4107_);
lean_dec(v_i_4107_);
v_res_4116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4105_, v_sz_boxed_4114_, v_i_boxed_4115_, v_b_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec_ref(v_as_4105_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4117_, lean_object* v_init_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_root_4124_; lean_object* v_tail_4125_; lean_object* v___x_4126_; 
v_root_4124_ = lean_ctor_get(v_t_4117_, 0);
v_tail_4125_ = lean_ctor_get(v_t_4117_, 1);
lean_inc_ref(v_init_4118_);
v___x_4126_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4118_, v_root_4124_, v_init_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec_ref(v_init_4118_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4163_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4163_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4163_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
if (lean_obj_tag(v_a_4127_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; 
v_a_4131_ = lean_ctor_get(v_a_4127_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v_a_4127_, 1);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v_a_4131_);
v___x_4133_ = v___x_4129_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; size_t v_sz_4138_; size_t v___x_4139_; lean_object* v___x_4140_; 
lean_del_object(v___x_4129_);
v_a_4135_ = lean_ctor_get(v_a_4127_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v_a_4127_, 1);
v___x_4136_ = lean_box(0);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v_a_4135_);
v_sz_4138_ = lean_array_size(v_tail_4125_);
v___x_4139_ = ((size_t)0ULL);
v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4125_, v_sz_4138_, v___x_4139_, v___x_4137_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4154_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v_fst_4145_; 
v_fst_4145_ = lean_ctor_get(v_a_4141_, 0);
if (lean_obj_tag(v_fst_4145_) == 0)
{
lean_object* v_snd_4146_; lean_object* v___x_4148_; 
v_snd_4146_ = lean_ctor_get(v_a_4141_, 1);
lean_inc(v_snd_4146_);
lean_dec(v_a_4141_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v_snd_4146_);
v___x_4148_ = v___x_4143_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_snd_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
else
{
lean_object* v_val_4150_; lean_object* v___x_4152_; 
lean_inc_ref(v_fst_4145_);
lean_dec(v_a_4141_);
v_val_4150_ = lean_ctor_get(v_fst_4145_, 0);
lean_inc(v_val_4150_);
lean_dec_ref_known(v_fst_4145_, 1);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v_val_4150_);
v___x_4152_ = v___x_4143_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_val_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4140_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4140_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_a_4164_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4126_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4126_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4172_, lean_object* v_init_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4172_, v_init_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_t_4172_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4180_, lean_object* v_fvarIds_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; 
lean_inc(v_goal_4180_);
v___x_4187_ = l_Lean_MVarId_getDecl(v_goal_4180_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v_lctx_4189_; lean_object* v_decls_4190_; lean_object* v___x_4191_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v_lctx_4189_ = lean_ctor_get(v_a_4188_, 1);
lean_inc_ref(v_lctx_4189_);
lean_dec(v_a_4188_);
v_decls_4190_ = lean_ctor_get(v_lctx_4189_, 1);
lean_inc_ref(v_decls_4190_);
lean_dec_ref(v_lctx_4189_);
v___x_4191_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4190_, v_fvarIds_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec_ref(v_decls_4190_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4191_, 1);
v___x_4193_ = l_Lean_MVarId_tryClearMany(v_goal_4180_, v_a_4192_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4192_);
return v___x_4193_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v_goal_4180_);
v_a_4194_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4191_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4191_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_fvarIds_4181_);
lean_dec(v_goal_4180_);
v_a_4202_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4187_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4187_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4210_, lean_object* v_fvarIds_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4210_, v_fvarIds_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4218_, size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4218_, v_sz_4219_, v_i_4220_, v_b_4221_, v___y_4223_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4228_, lean_object* v_sz_4229_, lean_object* v_i_4230_, lean_object* v_b_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
size_t v_sz_boxed_4237_; size_t v_i_boxed_4238_; lean_object* v_res_4239_; 
v_sz_boxed_4237_ = lean_unbox_usize(v_sz_4229_);
lean_dec(v_sz_4229_);
v_i_boxed_4238_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4228_, v_sz_boxed_4237_, v_i_boxed_4238_, v_b_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec_ref(v_as_4228_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4240_, size_t v_sz_4241_, size_t v_i_4242_, lean_object* v_b_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4240_, v_sz_4241_, v_i_4242_, v_b_4243_, v___y_4245_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4250_, lean_object* v_sz_4251_, lean_object* v_i_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
size_t v_sz_boxed_4259_; size_t v_i_boxed_4260_; lean_object* v_res_4261_; 
v_sz_boxed_4259_ = lean_unbox_usize(v_sz_4251_);
lean_dec(v_sz_4251_);
v_i_boxed_4260_ = lean_unbox_usize(v_i_4252_);
lean_dec(v_i_4252_);
v_res_4261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4250_, v_sz_boxed_4259_, v_i_boxed_4260_, v_b_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v_as_4250_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4262_, lean_object* v_as_4263_, size_t v_sz_4264_, size_t v_i_4265_, lean_object* v_b_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_usize_dec_lt(v_i_4265_, v_sz_4264_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v_b_4266_);
return v___x_4275_;
}
else
{
lean_object* v_a_4276_; lean_object* v_fst_4277_; lean_object* v_snd_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v_a_4276_ = lean_array_uget_borrowed(v_as_4263_, v_i_4265_);
v_fst_4277_ = lean_ctor_get(v_a_4276_, 0);
v_snd_4278_ = lean_ctor_get(v_a_4276_, 1);
lean_inc(v_snd_4278_);
v___x_4279_ = l_Lean_Meta_FVarSubst_get(v_fs_4262_, v_snd_4278_);
lean_inc(v_fst_4277_);
v___x_4280_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4277_, v___x_4279_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v___x_4281_; size_t v___x_4282_; size_t v___x_4283_; 
lean_dec_ref_known(v___x_4280_, 1);
v___x_4281_ = lean_box(0);
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = lean_usize_add(v_i_4265_, v___x_4282_);
v_i_4265_ = v___x_4283_;
v_b_4266_ = v___x_4281_;
goto _start;
}
else
{
return v___x_4280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4285_, lean_object* v_as_4286_, lean_object* v_sz_4287_, lean_object* v_i_4288_, lean_object* v_b_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
size_t v_sz_boxed_4297_; size_t v_i_boxed_4298_; lean_object* v_res_4299_; 
v_sz_boxed_4297_ = lean_unbox_usize(v_sz_4287_);
lean_dec(v_sz_4287_);
v_i_boxed_4298_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_res_4299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4285_, v_as_4286_, v_sz_boxed_4297_, v_i_boxed_4298_, v_b_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v_as_4286_);
lean_dec(v_fs_4285_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4300_, lean_object* v_toTag_4301_, size_t v_sz_4302_, size_t v___x_4303_, lean_object* v___x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4300_, v_toTag_4301_, v_sz_4302_, v___x_4303_, v___x_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; 
v_unused_4320_ = lean_ctor_get(v___x_4312_, 0);
lean_dec(v_unused_4320_);
v___x_4314_ = v___x_4312_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_dec(v___x_4312_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4304_);
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4304_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
else
{
return v___x_4312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4321_, lean_object* v_toTag_4322_, lean_object* v_sz_4323_, lean_object* v___x_4324_, lean_object* v___x_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
size_t v_sz_boxed_4333_; size_t v___x_1640__boxed_4334_; lean_object* v_res_4335_; 
v_sz_boxed_4333_ = lean_unbox_usize(v_sz_4323_);
lean_dec(v_sz_4323_);
v___x_1640__boxed_4334_ = lean_unbox_usize(v___x_4324_);
lean_dec(v___x_4324_);
v_res_4335_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4321_, v_toTag_4322_, v_sz_boxed_4333_, v___x_1640__boxed_4334_, v___x_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec_ref(v_toTag_4322_);
lean_dec(v_fs_4321_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4336_, size_t v_i_4337_, size_t v_stop_4338_, lean_object* v_b_4339_){
_start:
{
lean_object* v___y_4341_; uint8_t v___x_4345_; 
v___x_4345_ = lean_usize_dec_eq(v_i_4337_, v_stop_4338_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4346_ = lean_array_uget_borrowed(v_as_4336_, v_i_4337_);
v___x_4347_ = l_Lean_Expr_isFVar(v___x_4346_);
if (v___x_4347_ == 0)
{
v___y_4341_ = v_b_4339_;
goto v___jp_4340_;
}
else
{
lean_object* v___x_4348_; 
lean_inc(v___x_4346_);
v___x_4348_ = lean_array_push(v_b_4339_, v___x_4346_);
v___y_4341_ = v___x_4348_;
goto v___jp_4340_;
}
}
else
{
return v_b_4339_;
}
v___jp_4340_:
{
size_t v___x_4342_; size_t v___x_4343_; 
v___x_4342_ = ((size_t)1ULL);
v___x_4343_ = lean_usize_add(v_i_4337_, v___x_4342_);
v_i_4337_ = v___x_4343_;
v_b_4339_ = v___y_4341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4349_, lean_object* v_i_4350_, lean_object* v_stop_4351_, lean_object* v_b_4352_){
_start:
{
size_t v_i_boxed_4353_; size_t v_stop_boxed_4354_; lean_object* v_res_4355_; 
v_i_boxed_4353_ = lean_unbox_usize(v_i_4350_);
lean_dec(v_i_4350_);
v_stop_boxed_4354_ = lean_unbox_usize(v_stop_4351_);
lean_dec(v_stop_4351_);
v_res_4355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4349_, v_i_boxed_4353_, v_stop_boxed_4354_, v_b_4352_);
lean_dec_ref(v_as_4349_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4356_, size_t v_sz_4357_, size_t v_i_4358_, lean_object* v_bs_4359_){
_start:
{
uint8_t v___x_4360_; 
v___x_4360_ = lean_usize_dec_lt(v_i_4358_, v_sz_4357_);
if (v___x_4360_ == 0)
{
return v_bs_4359_;
}
else
{
lean_object* v_v_4361_; lean_object* v___x_4362_; lean_object* v_bs_x27_4363_; lean_object* v___x_4364_; size_t v___x_4365_; size_t v___x_4366_; lean_object* v___x_4367_; 
v_v_4361_ = lean_array_uget(v_bs_4359_, v_i_4358_);
v___x_4362_ = lean_unsigned_to_nat(0u);
v_bs_x27_4363_ = lean_array_uset(v_bs_4359_, v_i_4358_, v___x_4362_);
v___x_4364_ = l_Lean_Meta_FVarSubst_get(v_fs_4356_, v_v_4361_);
v___x_4365_ = ((size_t)1ULL);
v___x_4366_ = lean_usize_add(v_i_4358_, v___x_4365_);
v___x_4367_ = lean_array_uset(v_bs_x27_4363_, v_i_4358_, v___x_4364_);
v_i_4358_ = v___x_4366_;
v_bs_4359_ = v___x_4367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4369_, lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_bs_4372_){
_start:
{
size_t v_sz_boxed_4373_; size_t v_i_boxed_4374_; lean_object* v_res_4375_; 
v_sz_boxed_4373_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4374_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4369_, v_sz_boxed_4373_, v_i_boxed_4374_, v_bs_4372_);
lean_dec(v_fs_4369_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4376_, size_t v_i_4377_, lean_object* v_bs_4378_){
_start:
{
uint8_t v___x_4379_; 
v___x_4379_ = lean_usize_dec_lt(v_i_4377_, v_sz_4376_);
if (v___x_4379_ == 0)
{
return v_bs_4378_;
}
else
{
lean_object* v_v_4380_; lean_object* v___x_4381_; lean_object* v_bs_x27_4382_; lean_object* v___x_4383_; size_t v___x_4384_; size_t v___x_4385_; lean_object* v___x_4386_; 
v_v_4380_ = lean_array_uget(v_bs_4378_, v_i_4377_);
v___x_4381_ = lean_unsigned_to_nat(0u);
v_bs_x27_4382_ = lean_array_uset(v_bs_4378_, v_i_4377_, v___x_4381_);
v___x_4383_ = l_Lean_Expr_fvarId_x21(v_v_4380_);
lean_dec(v_v_4380_);
v___x_4384_ = ((size_t)1ULL);
v___x_4385_ = lean_usize_add(v_i_4377_, v___x_4384_);
v___x_4386_ = lean_array_uset(v_bs_x27_4382_, v_i_4377_, v___x_4383_);
v_i_4377_ = v___x_4385_;
v_bs_4378_ = v___x_4386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4388_, lean_object* v_i_4389_, lean_object* v_bs_4390_){
_start:
{
size_t v_sz_boxed_4391_; size_t v_i_boxed_4392_; lean_object* v_res_4393_; 
v_sz_boxed_4391_ = lean_unbox_usize(v_sz_4388_);
lean_dec(v_sz_4388_);
v_i_boxed_4392_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4391_, v_i_boxed_4392_, v_bs_4390_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4398_, lean_object* v_g_4399_, lean_object* v_fs_4400_, lean_object* v_clears_4401_, lean_object* v_gs_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v___y_4411_; size_t v_sz_4448_; size_t v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; 
v_sz_4448_ = lean_array_size(v_clears_4401_);
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4400_, v_sz_4448_, v___x_4449_, v_clears_4401_);
v___x_4451_ = lean_unsigned_to_nat(0u);
v___x_4452_ = lean_array_get_size(v___x_4450_);
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4454_ = lean_nat_dec_lt(v___x_4451_, v___x_4452_);
if (v___x_4454_ == 0)
{
lean_dec_ref(v___x_4450_);
v___y_4411_ = v___x_4453_;
goto v___jp_4410_;
}
else
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_nat_dec_le(v___x_4452_, v___x_4452_);
if (v___x_4455_ == 0)
{
if (v___x_4454_ == 0)
{
lean_dec_ref(v___x_4450_);
v___y_4411_ = v___x_4453_;
goto v___jp_4410_;
}
else
{
size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_usize_of_nat(v___x_4452_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4450_, v___x_4449_, v___x_4456_, v___x_4453_);
lean_dec_ref(v___x_4450_);
v___y_4411_ = v___x_4457_;
goto v___jp_4410_;
}
}
else
{
size_t v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_usize_of_nat(v___x_4452_);
v___x_4459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4450_, v___x_4449_, v___x_4458_, v___x_4453_);
lean_dec_ref(v___x_4450_);
v___y_4411_ = v___x_4459_;
goto v___jp_4410_;
}
}
v___jp_4410_:
{
size_t v_sz_4412_; size_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_sz_4412_ = lean_array_size(v___y_4411_);
v___x_4413_ = ((size_t)0ULL);
v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4412_, v___x_4413_, v___y_4411_);
v___x_4415_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4399_, v___x_4414_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; size_t v_sz_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___f_4421_; lean_object* v___x_4422_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc_n(v_a_4416_, 2);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = lean_box(0);
v_sz_4418_ = lean_array_size(v_toTag_4398_);
v___x_4419_ = lean_box_usize(v_sz_4418_);
v___x_4420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4421_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4421_, 0, v_fs_4400_);
lean_closure_set(v___f_4421_, 1, v_toTag_4398_);
lean_closure_set(v___f_4421_, 2, v___x_4419_);
lean_closure_set(v___f_4421_, 3, v___x_4420_);
lean_closure_set(v___f_4421_, 4, v___x_4417_);
v___x_4422_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4416_, v___f_4421_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4430_; 
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4430_ == 0)
{
lean_object* v_unused_4431_; 
v_unused_4431_ = lean_ctor_get(v___x_4422_, 0);
lean_dec(v_unused_4431_);
v___x_4424_ = v___x_4422_;
v_isShared_4425_ = v_isSharedCheck_4430_;
goto v_resetjp_4423_;
}
else
{
lean_dec(v___x_4422_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4430_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4426_ = lean_array_push(v_gs_4402_, v_a_4416_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4426_);
v___x_4428_ = v___x_4424_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_a_4416_);
lean_dec_ref(v_gs_4402_);
v_a_4432_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4422_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4422_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref(v_gs_4402_);
lean_dec(v_fs_4400_);
lean_dec_ref(v_toTag_4398_);
v_a_4440_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4415_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4415_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4460_, lean_object* v_g_4461_, lean_object* v_fs_4462_, lean_object* v_clears_4463_, lean_object* v_gs_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4460_, v_g_4461_, v_fs_4462_, v_clears_4463_, v_gs_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
return v_res_4472_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4473_ = lean_box(0);
v___x_4474_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
lean_ctor_set(v___x_4475_, 1, v___x_4473_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4533_);
v___x_4540_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4541_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4533_);
v___x_4542_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4533_);
v___x_4544_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4533_);
v___x_4546_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4533_);
v___x_4548_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4547_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4533_);
v___x_4550_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4533_);
v___x_4552_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4551_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; uint8_t v___x_4554_; 
v___x_4553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4533_);
v___x_4554_ = l_Lean_Syntax_isOfKind(v_stx_4533_, v___x_4553_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; 
lean_dec(v_stx_4533_);
v___x_4555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4555_;
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = lean_unsigned_to_nat(1u);
v___x_4557_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4556_);
v___x_4558_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4557_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4567_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4561_ = v___x_4558_;
v_isShared_4562_ = v_isSharedCheck_4567_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4567_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; lean_object* v___x_4565_; 
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v_stx_4533_);
lean_ctor_set(v___x_4563_, 1, v_a_4559_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4563_);
v___x_4565_ = v___x_4561_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
else
{
lean_dec(v_stx_4533_);
return v___x_4558_;
}
}
}
else
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v_ps_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4568_ = lean_unsigned_to_nat(1u);
v___x_4569_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4568_);
v_ps_4570_ = l_Lean_Syntax_getArgs(v___x_4569_);
lean_dec(v___x_4569_);
v___x_4571_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4570_);
lean_dec_ref(v_ps_4570_);
v___x_4572_ = lean_array_to_list(v___x_4571_);
v___x_4573_ = lean_box(0);
v___x_4574_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4572_, v___x_4573_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4583_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4583_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4583_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4579_, 0, v_stx_4533_);
lean_ctor_set(v___x_4579_, 1, v_a_4575_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4579_);
v___x_4581_ = v___x_4577_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec(v_stx_4533_);
v_a_4584_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4574_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4574_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
else
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4592_ = lean_unsigned_to_nat(1u);
v___x_4593_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4592_);
v___x_4594_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4593_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4603_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4597_ = v___x_4594_;
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4594_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4603_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4599_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4599_, 0, v_stx_4533_);
lean_ctor_set(v___x_4599_, 1, v_a_4595_);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 0, v___x_4599_);
v___x_4601_ = v___x_4597_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
else
{
lean_dec(v_stx_4533_);
return v___x_4594_;
}
}
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_stx_4533_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
}
else
{
lean_object* v___x_4606_; lean_object* v_h_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4606_ = lean_unsigned_to_nat(0u);
v_h_4607_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4606_);
lean_dec(v_stx_4533_);
v___x_4608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4607_);
v___x_4609_ = l_Lean_Syntax_isOfKind(v_h_4607_, v___x_4608_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; 
lean_dec(v_h_4607_);
v___x_4610_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4610_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4611_ = l_Lean_TSyntax_getId(v_h_4607_);
v___x_4612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4612_, 0, v_h_4607_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
return v___x_4613_;
}
}
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_stx_4533_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4617_ = lean_unsigned_to_nat(0u);
v___x_4618_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4617_);
lean_inc(v___x_4618_);
v___x_4619_ = l_Lean_Syntax_isOfKind(v___x_4618_, v___x_4539_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; 
lean_dec(v___x_4618_);
lean_dec(v_stx_4533_);
v___x_4620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4620_;
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4621_ = lean_unsigned_to_nat(1u);
v___x_4622_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4621_);
v___x_4623_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4622_);
v___x_4624_ = l_Lean_Syntax_matchesNull(v___x_4622_, v___x_4623_);
if (v___x_4624_ == 0)
{
uint8_t v___x_4625_; 
lean_dec(v_stx_4533_);
v___x_4625_ = l_Lean_Syntax_matchesNull(v___x_4622_, v___x_4617_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v___x_4618_);
v___x_4626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4626_;
}
else
{
v_stx_4533_ = v___x_4618_;
goto _start;
}
}
else
{
lean_object* v___x_4628_; 
v___x_4628_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4618_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4638_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4631_ = v___x_4628_;
v_isShared_4632_ = v_isSharedCheck_4638_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4638_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v_t_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v_t_4633_ = l_Lean_Syntax_getArg(v___x_4622_, v___x_4621_);
lean_dec(v___x_4622_);
v___x_4634_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4634_, 0, v_stx_4533_);
lean_ctor_set(v___x_4634_, 1, v_a_4629_);
lean_ctor_set(v___x_4634_, 2, v_t_4633_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4634_);
v___x_4636_ = v___x_4631_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
else
{
lean_dec(v___x_4622_);
lean_dec(v_stx_4533_);
return v___x_4628_;
}
}
}
}
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v_ps_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4639_ = lean_unsigned_to_nat(0u);
v___x_4640_ = l_Lean_Syntax_getArg(v_stx_4533_, v___x_4639_);
v_ps_4641_ = l_Lean_Syntax_getArgs(v___x_4640_);
lean_dec(v___x_4640_);
v___x_4642_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4641_);
lean_dec_ref(v_ps_4641_);
v___x_4643_ = lean_array_to_list(v___x_4642_);
v___x_4644_ = lean_box(0);
v___x_4645_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4643_, v___x_4644_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4654_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4648_ = v___x_4645_;
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4654_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4650_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4533_, v_a_4646_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 0, v___x_4650_);
v___x_4652_ = v___x_4648_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec(v_stx_4533_);
v_a_4655_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4645_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4645_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(lean_object* v_x_4663_, lean_object* v_x_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
if (lean_obj_tag(v_x_4663_) == 0)
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = l_List_reverse___redArg(v_x_4664_);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
else
{
lean_object* v_head_4672_; lean_object* v_tail_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4691_; 
v_head_4672_ = lean_ctor_get(v_x_4663_, 0);
v_tail_4673_ = lean_ctor_get(v_x_4663_, 1);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_x_4663_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4675_ = v_x_4663_;
v_isShared_4676_ = v_isSharedCheck_4691_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_tail_4673_);
lean_inc(v_head_4672_);
lean_dec(v_x_4663_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4691_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; 
v___x_4677_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_head_4672_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 1, v_x_4664_);
lean_ctor_set(v___x_4675_, 0, v_a_4678_);
v___x_4680_ = v___x_4675_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4678_);
lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_x_4664_);
v___x_4680_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
v_x_4663_ = v_tail_4673_;
v_x_4664_ = v___x_4680_;
goto _start;
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_del_object(v___x_4675_);
lean_dec(v_tail_4673_);
lean_dec(v_x_4664_);
v_a_4683_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4677_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4677_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1___boxed(lean_object* v_x_4692_, lean_object* v_x_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v_x_4692_, v_x_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___boxed(lean_object* v_stx_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_stx_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(lean_object* v_fst_4707_, lean_object* v_as_4708_, size_t v_sz_4709_, size_t v_i_4710_, lean_object* v_b_4711_){
_start:
{
lean_object* v_a_4714_; uint8_t v___x_4718_; 
v___x_4718_ = lean_usize_dec_lt(v_i_4710_, v_sz_4709_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; 
v___x_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4719_, 0, v_b_4711_);
return v___x_4719_;
}
else
{
lean_object* v_fst_4720_; lean_object* v_snd_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4743_; 
v_fst_4720_ = lean_ctor_get(v_b_4711_, 0);
v_snd_4721_ = lean_ctor_get(v_b_4711_, 1);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_b_4711_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4723_ = v_b_4711_;
v_isShared_4724_ = v_isSharedCheck_4743_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_snd_4721_);
lean_inc(v_fst_4720_);
lean_dec(v_b_4711_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4743_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_a_4735_; lean_object* v_expr_4736_; lean_object* v_hName_x3f_4737_; uint8_t v___y_4739_; uint8_t v___x_4742_; 
v_a_4735_ = lean_array_uget_borrowed(v_as_4708_, v_i_4710_);
v_expr_4736_ = lean_ctor_get(v_a_4735_, 0);
v_hName_x3f_4737_ = lean_ctor_get(v_a_4735_, 2);
v___x_4742_ = l_Lean_Expr_isFVar(v_expr_4736_);
if (v___x_4742_ == 0)
{
v___y_4739_ = v___x_4742_;
goto v___jp_4738_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4737_) == 0)
{
v___y_4739_ = v___x_4742_;
goto v___jp_4738_;
}
else
{
goto v___jp_4725_;
}
}
v___jp_4725_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = lean_array_get_borrowed(v___x_4726_, v_fst_4707_, v_snd_4721_);
lean_inc(v___x_4727_);
v___x_4728_ = l_Lean_mkFVar(v___x_4727_);
v___x_4729_ = lean_array_push(v_fst_4720_, v___x_4728_);
v___x_4730_ = lean_unsigned_to_nat(1u);
v___x_4731_ = lean_nat_add(v_snd_4721_, v___x_4730_);
lean_dec(v_snd_4721_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 1, v___x_4731_);
lean_ctor_set(v___x_4723_, 0, v___x_4729_);
v___x_4733_ = v___x_4723_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
v_a_4714_ = v___x_4733_;
goto v___jp_4713_;
}
}
v___jp_4738_:
{
if (v___y_4739_ == 0)
{
goto v___jp_4725_;
}
else
{
lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_del_object(v___x_4723_);
lean_inc_ref(v_expr_4736_);
v___x_4740_ = lean_array_push(v_fst_4720_, v_expr_4736_);
v___x_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set(v___x_4741_, 1, v_snd_4721_);
v_a_4714_ = v___x_4741_;
goto v___jp_4713_;
}
}
}
}
v___jp_4713_:
{
size_t v___x_4715_; size_t v___x_4716_; 
v___x_4715_ = ((size_t)1ULL);
v___x_4716_ = lean_usize_add(v_i_4710_, v___x_4715_);
v_i_4710_ = v___x_4716_;
v_b_4711_ = v_a_4714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg___boxed(lean_object* v_fst_4744_, lean_object* v_as_4745_, lean_object* v_sz_4746_, lean_object* v_i_4747_, lean_object* v_b_4748_, lean_object* v___y_4749_){
_start:
{
size_t v_sz_boxed_4750_; size_t v_i_boxed_4751_; lean_object* v_res_4752_; 
v_sz_boxed_4750_ = lean_unbox_usize(v_sz_4746_);
lean_dec(v_sz_4746_);
v_i_boxed_4751_ = lean_unbox_usize(v_i_4747_);
lean_dec(v_i_4747_);
v_res_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4744_, v_as_4745_, v_sz_boxed_4750_, v_i_boxed_4751_, v_b_4748_);
lean_dec_ref(v_as_4745_);
lean_dec_ref(v_fst_4744_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(lean_object* v_as_4753_, size_t v_i_4754_, size_t v_stop_4755_, lean_object* v_b_4756_){
_start:
{
lean_object* v___y_4758_; uint8_t v___x_4762_; 
v___x_4762_ = lean_usize_dec_eq(v_i_4754_, v_stop_4755_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; uint8_t v___y_4765_; lean_object* v_expr_4767_; lean_object* v_hName_x3f_4768_; uint8_t v___x_4769_; 
v___x_4763_ = lean_array_uget_borrowed(v_as_4753_, v_i_4754_);
v_expr_4767_ = lean_ctor_get(v___x_4763_, 0);
v_hName_x3f_4768_ = lean_ctor_get(v___x_4763_, 2);
v___x_4769_ = l_Lean_Expr_isFVar(v_expr_4767_);
if (v___x_4769_ == 0)
{
v___y_4765_ = v___x_4769_;
goto v___jp_4764_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4768_) == 0)
{
v___y_4765_ = v___x_4769_;
goto v___jp_4764_;
}
else
{
lean_object* v___x_4770_; 
lean_inc(v___x_4763_);
v___x_4770_ = lean_array_push(v_b_4756_, v___x_4763_);
v___y_4758_ = v___x_4770_;
goto v___jp_4757_;
}
}
v___jp_4764_:
{
if (v___y_4765_ == 0)
{
lean_object* v___x_4766_; 
lean_inc(v___x_4763_);
v___x_4766_ = lean_array_push(v_b_4756_, v___x_4763_);
v___y_4758_ = v___x_4766_;
goto v___jp_4757_;
}
else
{
v___y_4758_ = v_b_4756_;
goto v___jp_4757_;
}
}
}
else
{
return v_b_4756_;
}
v___jp_4757_:
{
size_t v___x_4759_; size_t v___x_4760_; 
v___x_4759_ = ((size_t)1ULL);
v___x_4760_ = lean_usize_add(v_i_4754_, v___x_4759_);
v_i_4754_ = v___x_4760_;
v_b_4756_ = v___y_4758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1___boxed(lean_object* v_as_4771_, lean_object* v_i_4772_, lean_object* v_stop_4773_, lean_object* v_b_4774_){
_start:
{
size_t v_i_boxed_4775_; size_t v_stop_boxed_4776_; lean_object* v_res_4777_; 
v_i_boxed_4775_ = lean_unbox_usize(v_i_4772_);
lean_dec(v_i_4772_);
v_stop_boxed_4776_ = lean_unbox_usize(v_stop_4773_);
lean_dec(v_stop_4773_);
v_res_4777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_as_4771_, v_i_boxed_4775_, v_stop_boxed_4776_, v_b_4774_);
lean_dec_ref(v_as_4771_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(lean_object* v_goal_4783_, lean_object* v_args_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v_lower_4794_; lean_object* v_upper_4795_; lean_object* v_j_4801_; lean_object* v___y_4803_; lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_j_4801_ = lean_unsigned_to_nat(0u);
v___x_4834_ = lean_array_get_size(v_args_4784_);
v___x_4835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__1));
v___x_4836_ = lean_nat_dec_lt(v_j_4801_, v___x_4834_);
if (v___x_4836_ == 0)
{
v___y_4803_ = v___x_4835_;
goto v___jp_4802_;
}
else
{
uint8_t v___x_4837_; 
v___x_4837_ = lean_nat_dec_le(v___x_4834_, v___x_4834_);
if (v___x_4837_ == 0)
{
if (v___x_4836_ == 0)
{
v___y_4803_ = v___x_4835_;
goto v___jp_4802_;
}
else
{
size_t v___x_4838_; size_t v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = ((size_t)0ULL);
v___x_4839_ = lean_usize_of_nat(v___x_4834_);
v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4784_, v___x_4838_, v___x_4839_, v___x_4835_);
v___y_4803_ = v___x_4840_;
goto v___jp_4802_;
}
}
else
{
size_t v___x_4841_; size_t v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = ((size_t)0ULL);
v___x_4842_ = lean_usize_of_nat(v___x_4834_);
v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__1(v_args_4784_, v___x_4841_, v___x_4842_, v___x_4835_);
v___y_4803_ = v___x_4843_;
goto v___jp_4802_;
}
}
v___jp_4790_:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4796_ = l_Array_toSubarray___redArg(v___y_4791_, v_lower_4794_, v_upper_4795_);
v___x_4797_ = l_Subarray_copy___redArg(v___x_4796_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
lean_ctor_set(v___x_4798_, 1, v___y_4792_);
v___x_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___y_4793_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
return v___x_4800_;
}
v___jp_4802_:
{
uint8_t v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = 3;
v___x_4805_ = l_Lean_MVarId_generalize(v_goal_4783_, v___y_4803_, v___x_4804_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v_fst_4807_; lean_object* v_snd_4808_; lean_object* v___x_4809_; size_t v_sz_4810_; size_t v___x_4811_; lean_object* v___x_4812_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4805_, 1);
v_fst_4807_ = lean_ctor_get(v_a_4806_, 0);
lean_inc(v_fst_4807_);
v_snd_4808_ = lean_ctor_get(v_a_4806_, 1);
lean_inc(v_snd_4808_);
lean_dec(v_a_4806_);
v___x_4809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___closed__0));
v_sz_4810_ = lean_array_size(v_args_4784_);
v___x_4811_ = ((size_t)0ULL);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4807_, v_args_4784_, v_sz_4810_, v___x_4811_, v___x_4809_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v_fst_4814_; lean_object* v_snd_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_a_4813_);
lean_dec_ref_known(v___x_4812_, 1);
v_fst_4814_ = lean_ctor_get(v_a_4813_, 0);
lean_inc(v_fst_4814_);
v_snd_4815_ = lean_ctor_get(v_a_4813_, 1);
lean_inc(v_snd_4815_);
lean_dec(v_a_4813_);
v___x_4816_ = lean_array_get_size(v_fst_4807_);
v___x_4817_ = lean_nat_dec_le(v_snd_4815_, v_j_4801_);
if (v___x_4817_ == 0)
{
v___y_4791_ = v_fst_4807_;
v___y_4792_ = v_snd_4808_;
v___y_4793_ = v_fst_4814_;
v_lower_4794_ = v_snd_4815_;
v_upper_4795_ = v___x_4816_;
goto v___jp_4790_;
}
else
{
lean_dec(v_snd_4815_);
v___y_4791_ = v_fst_4807_;
v___y_4792_ = v_snd_4808_;
v___y_4793_ = v_fst_4814_;
v_lower_4794_ = v_j_4801_;
v_upper_4795_ = v___x_4816_;
goto v___jp_4790_;
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec(v_snd_4808_);
lean_dec(v_fst_4807_);
v_a_4818_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4812_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4812_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4805_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4805_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar___boxed(lean_object* v_goal_4844_, lean_object* v_args_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_goal_4844_, v_args_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec_ref(v_args_4845_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(lean_object* v_fst_4852_, lean_object* v_as_4853_, size_t v_sz_4854_, size_t v_i_4855_, lean_object* v_b_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___redArg(v_fst_4852_, v_as_4853_, v_sz_4854_, v_i_4855_, v_b_4856_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0___boxed(lean_object* v_fst_4863_, lean_object* v_as_4864_, lean_object* v_sz_4865_, lean_object* v_i_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
size_t v_sz_boxed_4873_; size_t v_i_boxed_4874_; lean_object* v_res_4875_; 
v_sz_boxed_4873_ = lean_unbox_usize(v_sz_4865_);
lean_dec(v_sz_4865_);
v_i_boxed_4874_ = lean_unbox_usize(v_i_4866_);
lean_dec(v_i_4866_);
v_res_4875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar_spec__0(v_fst_4863_, v_as_4864_, v_sz_boxed_4873_, v_i_boxed_4874_, v_b_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec_ref(v_as_4864_);
lean_dec_ref(v_fst_4863_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(lean_object* v_as_4876_, size_t v_i_4877_, size_t v_stop_4878_, lean_object* v_b_4879_){
_start:
{
lean_object* v___y_4881_; uint8_t v___x_4885_; 
v___x_4885_ = lean_usize_dec_eq(v_i_4877_, v_stop_4878_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4886_; lean_object* v_fst_4887_; 
v___x_4886_ = lean_array_uget_borrowed(v_as_4876_, v_i_4877_);
v_fst_4887_ = lean_ctor_get(v___x_4886_, 0);
if (lean_obj_tag(v_fst_4887_) == 0)
{
v___y_4881_ = v_b_4879_;
goto v___jp_4880_;
}
else
{
lean_object* v_val_4888_; lean_object* v___x_4889_; 
v_val_4888_ = lean_ctor_get(v_fst_4887_, 0);
lean_inc(v_val_4888_);
v___x_4889_ = lean_array_push(v_b_4879_, v_val_4888_);
v___y_4881_ = v___x_4889_;
goto v___jp_4880_;
}
}
else
{
return v_b_4879_;
}
v___jp_4880_:
{
size_t v___x_4882_; size_t v___x_4883_; 
v___x_4882_ = ((size_t)1ULL);
v___x_4883_ = lean_usize_add(v_i_4877_, v___x_4882_);
v_i_4877_ = v___x_4883_;
v_b_4879_ = v___y_4881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1___boxed(lean_object* v_as_4890_, lean_object* v_i_4891_, lean_object* v_stop_4892_, lean_object* v_b_4893_){
_start:
{
size_t v_i_boxed_4894_; size_t v_stop_boxed_4895_; lean_object* v_res_4896_; 
v_i_boxed_4894_ = lean_unbox_usize(v_i_4891_);
lean_dec(v_i_4891_);
v_stop_boxed_4895_ = lean_unbox_usize(v_stop_4892_);
lean_dec(v_stop_4892_);
v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4890_, v_i_boxed_4894_, v_stop_boxed_4895_, v_b_4893_);
lean_dec_ref(v_as_4890_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(lean_object* v_as_4899_, lean_object* v_start_4900_, lean_object* v_stop_4901_){
_start:
{
lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4902_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___closed__0));
v___x_4903_ = lean_nat_dec_lt(v_start_4900_, v_stop_4901_);
if (v___x_4903_ == 0)
{
return v___x_4902_;
}
else
{
lean_object* v___x_4904_; uint8_t v___x_4905_; 
v___x_4904_ = lean_array_get_size(v_as_4899_);
v___x_4905_ = lean_nat_dec_le(v_stop_4901_, v___x_4904_);
if (v___x_4905_ == 0)
{
uint8_t v___x_4906_; 
v___x_4906_ = lean_nat_dec_lt(v_start_4900_, v___x_4904_);
if (v___x_4906_ == 0)
{
return v___x_4902_;
}
else
{
size_t v___x_4907_; size_t v___x_4908_; lean_object* v___x_4909_; 
v___x_4907_ = lean_usize_of_nat(v_start_4900_);
v___x_4908_ = lean_usize_of_nat(v___x_4904_);
v___x_4909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4899_, v___x_4907_, v___x_4908_, v___x_4902_);
return v___x_4909_;
}
}
else
{
size_t v___x_4910_; size_t v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = lean_usize_of_nat(v_start_4900_);
v___x_4911_ = lean_usize_of_nat(v_stop_4901_);
v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1_spec__1(v_as_4899_, v___x_4910_, v___x_4911_, v___x_4902_);
return v___x_4912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1___boxed(lean_object* v_as_4913_, lean_object* v_start_4914_, lean_object* v_stop_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_as_4913_, v_start_4914_, v_stop_4915_);
lean_dec(v_stop_4915_);
lean_dec(v_start_4914_);
lean_dec_ref(v_as_4913_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(lean_object* v_as_4917_, lean_object* v_bs_4918_, lean_object* v_i_4919_, lean_object* v_cs_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___y_4929_; lean_object* v___y_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___x_4939_; uint8_t v___x_4940_; 
v___x_4939_ = lean_array_get_size(v_as_4917_);
v___x_4940_ = lean_nat_dec_lt(v_i_4919_, v___x_4939_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; 
lean_dec(v_i_4919_);
v___x_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4941_, 0, v_cs_4920_);
return v___x_4941_;
}
else
{
lean_object* v___x_4942_; uint8_t v___x_4943_; 
v___x_4942_ = lean_array_get_size(v_bs_4918_);
v___x_4943_ = lean_nat_dec_lt(v_i_4919_, v___x_4942_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; 
lean_dec(v_i_4919_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v_cs_4920_);
return v___x_4944_;
}
else
{
lean_object* v_a_4945_; lean_object* v_fst_4946_; lean_object* v_snd_4947_; lean_object* v_fst_4949_; lean_object* v_snd_4950_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4954_; lean_object* v___y_4955_; lean_object* v___y_4956_; lean_object* v_b_4988_; 
v_a_4945_ = lean_array_fget_borrowed(v_as_4917_, v_i_4919_);
v_fst_4946_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_fst_4946_);
v_snd_4947_ = lean_ctor_get(v_a_4945_, 1);
v_b_4988_ = lean_array_fget(v_bs_4918_, v_i_4919_);
if (lean_obj_tag(v_b_4988_) == 4)
{
lean_object* v_ref_4989_; lean_object* v_a_4990_; lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5037_; 
v_ref_4989_ = lean_ctor_get(v_b_4988_, 0);
v_a_4990_ = lean_ctor_get(v_b_4988_, 1);
v_a_4991_ = lean_ctor_get(v_b_4988_, 2);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_b_4988_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_4993_ = v_b_4988_;
v_isShared_4994_ = v_isSharedCheck_5037_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_inc(v_a_4990_);
lean_inc(v_ref_4989_);
lean_dec(v_b_4988_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5037_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v_fileName_4995_; lean_object* v_fileMap_4996_; lean_object* v_options_4997_; lean_object* v_currRecDepth_4998_; lean_object* v_maxRecDepth_4999_; lean_object* v_ref_5000_; lean_object* v_currNamespace_5001_; lean_object* v_openDecls_5002_; lean_object* v_initHeartbeats_5003_; lean_object* v_maxHeartbeats_5004_; lean_object* v_quotContext_5005_; lean_object* v_currMacroScope_5006_; uint8_t v_diag_5007_; lean_object* v_cancelTk_x3f_5008_; uint8_t v_suppressElabErrors_5009_; lean_object* v_inheritedTraceOptions_5010_; lean_object* v_ref_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v_fileName_4995_ = lean_ctor_get(v___y_4925_, 0);
v_fileMap_4996_ = lean_ctor_get(v___y_4925_, 1);
v_options_4997_ = lean_ctor_get(v___y_4925_, 2);
v_currRecDepth_4998_ = lean_ctor_get(v___y_4925_, 3);
v_maxRecDepth_4999_ = lean_ctor_get(v___y_4925_, 4);
v_ref_5000_ = lean_ctor_get(v___y_4925_, 5);
v_currNamespace_5001_ = lean_ctor_get(v___y_4925_, 6);
v_openDecls_5002_ = lean_ctor_get(v___y_4925_, 7);
v_initHeartbeats_5003_ = lean_ctor_get(v___y_4925_, 8);
v_maxHeartbeats_5004_ = lean_ctor_get(v___y_4925_, 9);
v_quotContext_5005_ = lean_ctor_get(v___y_4925_, 10);
v_currMacroScope_5006_ = lean_ctor_get(v___y_4925_, 11);
v_diag_5007_ = lean_ctor_get_uint8(v___y_4925_, sizeof(void*)*14);
v_cancelTk_x3f_5008_ = lean_ctor_get(v___y_4925_, 12);
v_suppressElabErrors_5009_ = lean_ctor_get_uint8(v___y_4925_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5010_ = lean_ctor_get(v___y_4925_, 13);
v_ref_5011_ = l_Lean_replaceRef(v_ref_4989_, v_ref_5000_);
lean_inc_ref(v_inheritedTraceOptions_5010_);
lean_inc(v_cancelTk_x3f_5008_);
lean_inc(v_currMacroScope_5006_);
lean_inc(v_quotContext_5005_);
lean_inc(v_maxHeartbeats_5004_);
lean_inc(v_initHeartbeats_5003_);
lean_inc(v_openDecls_5002_);
lean_inc(v_currNamespace_5001_);
lean_inc(v_maxRecDepth_4999_);
lean_inc(v_currRecDepth_4998_);
lean_inc_ref(v_options_4997_);
lean_inc_ref(v_fileMap_4996_);
lean_inc_ref(v_fileName_4995_);
v___x_5012_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5012_, 0, v_fileName_4995_);
lean_ctor_set(v___x_5012_, 1, v_fileMap_4996_);
lean_ctor_set(v___x_5012_, 2, v_options_4997_);
lean_ctor_set(v___x_5012_, 3, v_currRecDepth_4998_);
lean_ctor_set(v___x_5012_, 4, v_maxRecDepth_4999_);
lean_ctor_set(v___x_5012_, 5, v_ref_5011_);
lean_ctor_set(v___x_5012_, 6, v_currNamespace_5001_);
lean_ctor_set(v___x_5012_, 7, v_openDecls_5002_);
lean_ctor_set(v___x_5012_, 8, v_initHeartbeats_5003_);
lean_ctor_set(v___x_5012_, 9, v_maxHeartbeats_5004_);
lean_ctor_set(v___x_5012_, 10, v_quotContext_5005_);
lean_ctor_set(v___x_5012_, 11, v_currMacroScope_5006_);
lean_ctor_set(v___x_5012_, 12, v_cancelTk_x3f_5008_);
lean_ctor_set(v___x_5012_, 13, v_inheritedTraceOptions_5010_);
lean_ctor_set_uint8(v___x_5012_, sizeof(void*)*14, v_diag_5007_);
lean_ctor_set_uint8(v___x_5012_, sizeof(void*)*14 + 1, v_suppressElabErrors_5009_);
v___x_5013_ = l_Lean_Elab_Term_elabType(v_a_4991_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___x_5012_, v___y_4926_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5015_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc_n(v_a_5014_, 2);
lean_dec_ref_known(v___x_5013_, 1);
v___x_5015_ = l_Lean_Elab_Term_exprToSyntax(v_a_5014_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___x_5012_, v___y_4926_);
lean_dec_ref_known(v___x_5012_, 14);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5018_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
lean_dec_ref_known(v___x_5015_, 1);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 2, v_a_5016_);
v___x_5018_ = v___x_4993_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_ref_4989_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v_a_4990_);
lean_ctor_set(v_reuseFailAlloc_5020_, 2, v_a_5016_);
v___x_5018_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5019_; 
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v_a_5014_);
v_fst_4949_ = v___x_5018_;
v_snd_4950_ = v___x_5019_;
v___y_4951_ = v___y_4921_;
v___y_4952_ = v___y_4922_;
v___y_4953_ = v___y_4923_;
v___y_4954_ = v___y_4924_;
v___y_4955_ = v___y_4925_;
v___y_4956_ = v___y_4926_;
goto v___jp_4948_;
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_5014_);
lean_del_object(v___x_4993_);
lean_dec_ref(v_a_4990_);
lean_dec(v_ref_4989_);
lean_dec(v_fst_4946_);
lean_dec_ref(v_cs_4920_);
lean_dec(v_i_4919_);
v_a_5021_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5015_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5015_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec_ref_known(v___x_5012_, 14);
lean_del_object(v___x_4993_);
lean_dec_ref(v_a_4990_);
lean_dec(v_ref_4989_);
lean_dec(v_fst_4946_);
lean_dec_ref(v_cs_4920_);
lean_dec(v_i_4919_);
v_a_5029_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5013_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5013_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
else
{
lean_object* v___x_5038_; 
v___x_5038_ = lean_box(0);
v_fst_4949_ = v_b_4988_;
v_snd_4950_ = v___x_5038_;
v___y_4951_ = v___y_4921_;
v___y_4952_ = v___y_4922_;
v___y_4953_ = v___y_4923_;
v___y_4954_ = v___y_4924_;
v___y_4955_ = v___y_4925_;
v___y_4956_ = v___y_4926_;
goto v___jp_4948_;
}
v___jp_4948_:
{
lean_object* v___x_4957_; 
lean_inc(v_snd_4950_);
lean_inc(v_snd_4947_);
v___x_4957_ = l_Lean_Elab_Term_elabTerm(v_snd_4947_, v_snd_4950_, v___x_4943_, v___x_4943_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4959_ = lean_box(0);
v___x_4960_ = l_Lean_Elab_Term_ensureHasType(v_snd_4950_, v_a_4958_, v___x_4959_, v___x_4959_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_fst_4949_);
if (lean_obj_tag(v_fst_4946_) == 0)
{
v___y_4929_ = v_fst_4949_;
v___y_4930_ = v___x_4962_;
v___y_4931_ = v_a_4961_;
v___y_4932_ = v___x_4959_;
goto v___jp_4928_;
}
else
{
lean_object* v_val_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4971_; 
v_val_4963_ = lean_ctor_get(v_fst_4946_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v_fst_4946_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4965_ = v_fst_4946_;
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_val_4963_);
lean_dec(v_fst_4946_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4967_ = l_Lean_TSyntax_getId(v_val_4963_);
lean_dec(v_val_4963_);
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 0, v___x_4967_);
v___x_4969_ = v___x_4965_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4967_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
v___y_4929_ = v_fst_4949_;
v___y_4930_ = v___x_4962_;
v___y_4931_ = v_a_4961_;
v___y_4932_ = v___x_4969_;
goto v___jp_4928_;
}
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_dec_ref(v_fst_4949_);
lean_dec(v_fst_4946_);
lean_dec_ref(v_cs_4920_);
lean_dec(v_i_4919_);
v_a_4972_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4960_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4960_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
else
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4987_; 
lean_dec(v_snd_4950_);
lean_dec_ref(v_fst_4949_);
lean_dec(v_fst_4946_);
lean_dec_ref(v_cs_4920_);
lean_dec(v_i_4919_);
v_a_4980_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4957_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4957_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4983_ == 0)
{
v___x_4985_ = v___x_4982_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
}
}
v___jp_4928_:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4933_, 0, v___y_4931_);
lean_ctor_set(v___x_4933_, 1, v___y_4930_);
lean_ctor_set(v___x_4933_, 2, v___y_4932_);
v___x_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___y_4929_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = lean_unsigned_to_nat(1u);
v___x_4936_ = lean_nat_add(v_i_4919_, v___x_4935_);
lean_dec(v_i_4919_);
v___x_4937_ = lean_array_push(v_cs_4920_, v___x_4934_);
v_i_4919_ = v___x_4936_;
v_cs_4920_ = v___x_4937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0___boxed(lean_object* v_as_5039_, lean_object* v_bs_5040_, lean_object* v_i_5041_, lean_object* v_cs_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_as_5039_, v_bs_5040_, v_i_5041_, v_cs_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec_ref(v_bs_5040_);
lean_dec_ref(v_as_5039_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0(lean_object* v_tgts_5053_, lean_object* v_g_5054_, lean_object* v_pats_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5063_ = lean_array_mk(v_pats_5055_);
v___x_5064_ = lean_unsigned_to_nat(0u);
v___x_5065_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___closed__0));
v___x_5066_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_RCases_rcases_spec__0(v_tgts_5053_, v___x_5063_, v___x_5064_, v___x_5065_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec_ref(v___x_5063_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v_fst_5069_; lean_object* v_snd_5070_; lean_object* v___x_5071_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = l_Array_unzip___redArg(v_a_5067_);
lean_dec(v_a_5067_);
v_fst_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_fst_5069_);
v_snd_5070_ = lean_ctor_get(v___x_5068_, 1);
lean_inc(v_snd_5070_);
lean_dec_ref(v___x_5068_);
v___x_5071_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_generalizeExceptFVar(v_g_5054_, v_snd_5070_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v_snd_5070_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v_a_5072_; lean_object* v_snd_5073_; lean_object* v_fst_5074_; lean_object* v_fst_5075_; lean_object* v_snd_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_5071_, 1);
v_snd_5073_ = lean_ctor_get(v_a_5072_, 1);
lean_inc(v_snd_5073_);
v_fst_5074_ = lean_ctor_get(v_a_5072_, 0);
lean_inc(v_fst_5074_);
lean_dec(v_a_5072_);
v_fst_5075_ = lean_ctor_get(v_snd_5073_, 0);
lean_inc(v_fst_5075_);
v_snd_5076_ = lean_ctor_get(v_snd_5073_, 1);
lean_inc(v_snd_5076_);
lean_dec(v_snd_5073_);
v___x_5077_ = lean_array_get_size(v_tgts_5053_);
v___x_5078_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_RCases_rcases_spec__1(v_tgts_5053_, v___x_5064_, v___x_5077_);
v___x_5079_ = l_Array_zip___redArg(v___x_5078_, v_fst_5075_);
lean_dec(v_fst_5075_);
lean_dec_ref(v___x_5078_);
v___x_5080_ = lean_box(0);
v___x_5081_ = l_Array_zip___redArg(v_fst_5069_, v_fst_5074_);
lean_dec(v_fst_5074_);
lean_dec(v_fst_5069_);
v___x_5082_ = lean_array_to_list(v___x_5081_);
v___x_5083_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed), 12, 1);
lean_closure_set(v___x_5083_, 0, v___x_5079_);
v___x_5084_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_snd_5076_, v___x_5080_, v___x_5065_, v___x_5065_, v___x_5082_, v___x_5083_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5093_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5087_ = v___x_5084_;
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5084_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5089_ = lean_array_to_list(v_a_5085_);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5089_);
v___x_5091_ = v___x_5087_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
v_a_5094_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5084_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5084_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
else
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
lean_dec(v_fst_5069_);
v_a_5102_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5104_ = v___x_5071_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5071_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v_g_5054_);
v_a_5110_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5066_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5066_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed(lean_object* v_tgts_5118_, lean_object* v_g_5119_, lean_object* v_pats_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_Elab_Tactic_RCases_rcases___lam__0(v_tgts_5118_, v_g_5119_, v_pats_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec_ref(v_tgts_5118_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(size_t v_sz_5133_, size_t v_i_5134_, lean_object* v_bs_5135_){
_start:
{
uint8_t v___x_5136_; 
v___x_5136_ = lean_usize_dec_lt(v_i_5134_, v_sz_5133_);
if (v___x_5136_ == 0)
{
return v_bs_5135_;
}
else
{
lean_object* v___x_5137_; lean_object* v_bs_x27_5138_; lean_object* v___x_5139_; size_t v___x_5140_; size_t v___x_5141_; lean_object* v___x_5142_; 
v___x_5137_ = lean_unsigned_to_nat(0u);
v_bs_x27_5138_ = lean_array_uset(v_bs_5135_, v_i_5134_, v___x_5137_);
v___x_5139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___closed__0));
v___x_5140_ = ((size_t)1ULL);
v___x_5141_ = lean_usize_add(v_i_5134_, v___x_5140_);
v___x_5142_ = lean_array_uset(v_bs_x27_5138_, v_i_5134_, v___x_5139_);
v_i_5134_ = v___x_5141_;
v_bs_5135_ = v___x_5142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v_sz_5144_, lean_object* v_i_5145_, lean_object* v_bs_5146_){
_start:
{
size_t v_sz_boxed_5147_; size_t v_i_boxed_5148_; lean_object* v_res_5149_; 
v_sz_boxed_5147_ = lean_unbox_usize(v_sz_5144_);
lean_dec(v_sz_5144_);
v_i_boxed_5148_ = lean_unbox_usize(v_i_5145_);
lean_dec(v_i_5145_);
v_res_5149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v_sz_boxed_5147_, v_i_boxed_5148_, v_bs_5146_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5150_, lean_object* v___x_5151_, lean_object* v_pat_5152_, lean_object* v_tgts_5153_, lean_object* v___x_5154_, lean_object* v___f_5155_, lean_object* v_g_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
if (v___x_5150_ == 0)
{
lean_object* v___x_5164_; uint8_t v___x_5165_; lean_object* v___y_5167_; 
lean_dec(v_g_5156_);
v___x_5164_ = lean_unsigned_to_nat(1u);
v___x_5165_ = lean_nat_dec_eq(v___x_5151_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_object* v_ref_5176_; 
v_ref_5176_ = lean_ctor_get(v_pat_5152_, 0);
lean_inc(v_ref_5176_);
v___y_5167_ = v_ref_5176_;
goto v___jp_5166_;
}
else
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
lean_dec_ref(v_tgts_5153_);
v___x_5177_ = lean_box(0);
v___x_5178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5178_, 0, v_pat_5152_);
lean_ctor_set(v___x_5178_, 1, v___x_5177_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc(v___y_5160_);
lean_inc_ref(v___y_5159_);
lean_inc(v___y_5158_);
lean_inc_ref(v___y_5157_);
v___x_5179_ = lean_apply_8(v___f_5155_, v___x_5178_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, lean_box(0));
return v___x_5179_;
}
v___jp_5166_:
{
lean_object* v___x_5168_; lean_object* v_snd_5169_; size_t v_sz_5170_; size_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v_snd_5174_; lean_object* v___x_5175_; 
v___x_5168_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5152_);
v_snd_5169_ = lean_ctor_get(v___x_5168_, 1);
lean_inc(v_snd_5169_);
lean_dec_ref(v___x_5168_);
v_sz_5170_ = lean_array_size(v_tgts_5153_);
v___x_5171_ = ((size_t)0ULL);
v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v_sz_5170_, v___x_5171_, v_tgts_5153_);
v___x_5173_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5167_, v___x_5172_, v___x_5165_, v___x_5154_, v_snd_5169_);
lean_dec_ref(v___x_5172_);
v_snd_5174_ = lean_ctor_get(v___x_5173_, 1);
lean_inc(v_snd_5174_);
lean_dec_ref(v___x_5173_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc(v___y_5160_);
lean_inc_ref(v___y_5159_);
lean_inc(v___y_5158_);
lean_inc_ref(v___y_5157_);
v___x_5175_ = lean_apply_8(v___f_5155_, v_snd_5174_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, lean_box(0));
return v___x_5175_;
}
}
else
{
lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_dec_ref(v___f_5155_);
lean_dec_ref(v_tgts_5153_);
lean_dec_ref(v_pat_5152_);
v___x_5180_ = lean_box(0);
v___x_5181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5181_, 0, v_g_5156_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
return v___x_5182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5183_, lean_object* v___x_5184_, lean_object* v_pat_5185_, lean_object* v_tgts_5186_, lean_object* v___x_5187_, lean_object* v___f_5188_, lean_object* v_g_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
uint8_t v___x_5325__boxed_5197_; lean_object* v_res_5198_; 
v___x_5325__boxed_5197_ = lean_unbox(v___x_5183_);
v_res_5198_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5325__boxed_5197_, v___x_5184_, v_pat_5185_, v_tgts_5186_, v___x_5187_, v___f_5188_, v_g_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___x_5187_);
lean_dec(v___x_5184_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5199_, lean_object* v_pat_5200_, lean_object* v_g_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v___f_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v___y_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; 
lean_inc(v_g_5201_);
lean_inc_ref(v_tgts_5199_);
v___f_5209_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5209_, 0, v_tgts_5199_);
lean_closure_set(v___f_5209_, 1, v_g_5201_);
v___x_5210_ = lean_array_get_size(v_tgts_5199_);
v___x_5211_ = lean_unsigned_to_nat(0u);
v___x_5212_ = lean_nat_dec_eq(v___x_5210_, v___x_5211_);
v___x_5213_ = lean_box(v___x_5212_);
v___y_5214_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5214_, 0, v___x_5213_);
lean_closure_set(v___y_5214_, 1, v___x_5210_);
lean_closure_set(v___y_5214_, 2, v_pat_5200_);
lean_closure_set(v___y_5214_, 3, v_tgts_5199_);
lean_closure_set(v___y_5214_, 4, v___x_5211_);
lean_closure_set(v___y_5214_, 5, v___f_5209_);
lean_closure_set(v___y_5214_, 6, v_g_5201_);
v___x_5215_ = 1;
v___x_5216_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5214_, v___x_5215_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5217_, lean_object* v_pat_5218_, lean_object* v_g_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5217_, v_pat_5218_, v_g_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5232_, lean_object* v_g_5233_, lean_object* v_pat_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Lean_Elab_Term_elabType(v_ty_5232_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc_n(v_a_5243_, 2);
lean_dec_ref_known(v___x_5242_, 1);
v___x_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5244_, 0, v_a_5243_);
v___x_5245_ = 0;
v___x_5246_ = lean_box(0);
v___x_5247_ = l_Lean_Meta_mkFreshExprMVar(v___x_5244_, v___x_5245_, v___x_5246_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___y_5250_; lean_object* v___x_5304_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v___x_5304_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5234_);
if (lean_obj_tag(v___x_5304_) == 0)
{
v___y_5250_ = v___x_5246_;
goto v___jp_5249_;
}
else
{
lean_object* v_val_5305_; 
v_val_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_val_5305_);
lean_dec_ref_known(v___x_5304_, 1);
v___y_5250_ = v_val_5305_;
goto v___jp_5249_;
}
v___jp_5249_:
{
lean_object* v___x_5251_; 
lean_inc(v_a_5248_);
v___x_5251_ = l_Lean_MVarId_assert(v_g_5233_, v___y_5250_, v_a_5243_, v_a_5248_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
if (lean_obj_tag(v___x_5251_) == 0)
{
lean_object* v_a_5252_; uint8_t v___x_5253_; lean_object* v___x_5254_; 
v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
lean_inc(v_a_5252_);
lean_dec_ref_known(v___x_5251_, 1);
v___x_5253_ = 0;
v___x_5254_ = l_Lean_Meta_intro1Core(v_a_5252_, v___x_5253_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v_fst_5256_; lean_object* v_snd_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5287_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_a_5255_);
lean_dec_ref_known(v___x_5254_, 1);
v_fst_5256_ = lean_ctor_get(v_a_5255_, 0);
v_snd_5257_ = lean_ctor_get(v_a_5255_, 1);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_a_5255_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5259_ = v_a_5255_;
v_isShared_5260_ = v_isSharedCheck_5287_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_snd_5257_);
lean_inc(v_fst_5256_);
lean_dec(v_a_5255_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5287_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5261_ = lean_box(0);
v___x_5262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5263_ = l_Lean_Expr_fvar___override(v_fst_5256_);
v___x_5264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5265_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5257_, v___x_5261_, v___x_5262_, v___x_5263_, v___x_5262_, v_pat_5234_, v___x_5264_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
lean_dec_ref(v___x_5263_);
if (lean_obj_tag(v___x_5265_) == 0)
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5278_; 
v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5268_ = v___x_5265_;
v_isShared_5269_ = v_isSharedCheck_5278_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5265_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5278_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5273_; 
v___x_5270_ = l_Lean_Expr_mvarId_x21(v_a_5248_);
lean_dec(v_a_5248_);
v___x_5271_ = lean_array_to_list(v_a_5266_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set_tag(v___x_5259_, 1);
lean_ctor_set(v___x_5259_, 1, v___x_5271_);
lean_ctor_set(v___x_5259_, 0, v___x_5270_);
v___x_5273_ = v___x_5259_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v___x_5270_);
lean_ctor_set(v_reuseFailAlloc_5277_, 1, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5275_; 
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 0, v___x_5273_);
v___x_5275_ = v___x_5268_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5286_; 
lean_del_object(v___x_5259_);
lean_dec(v_a_5248_);
v_a_5279_ = lean_ctor_get(v___x_5265_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5281_ = v___x_5265_;
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5265_);
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
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_dec(v_a_5248_);
lean_dec_ref(v_pat_5234_);
v_a_5288_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5254_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5254_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec(v_a_5248_);
lean_dec_ref(v_pat_5234_);
v_a_5296_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5251_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5251_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_dec(v_a_5243_);
lean_dec_ref(v_pat_5234_);
lean_dec(v_g_5233_);
v_a_5306_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5247_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5247_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_dec_ref(v_pat_5234_);
lean_dec(v_g_5233_);
v_a_5314_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5242_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5242_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5322_, lean_object* v_g_5323_, lean_object* v_pat_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5322_, v_g_5323_, v_pat_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5333_, lean_object* v_ty_5334_, lean_object* v_g_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_){
_start:
{
lean_object* v___f_5343_; uint8_t v___x_5344_; lean_object* v___x_5345_; 
v___f_5343_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5343_, 0, v_ty_5334_);
lean_closure_set(v___f_5343_, 1, v_g_5335_);
lean_closure_set(v___f_5343_, 2, v_pat_5333_);
v___x_5344_ = 1;
v___x_5345_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5343_, v___x_5344_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5346_, lean_object* v_ty_5347_, lean_object* v_g_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5346_, v_ty_5347_, v_g_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5364_, lean_object* v_acc_5365_, lean_object* v_ty_x3f_5366_){
_start:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; uint8_t v___x_5369_; 
v___x_5367_ = lean_unsigned_to_nat(0u);
v___x_5368_ = lean_array_get_size(v_pats_5364_);
v___x_5369_ = lean_nat_dec_lt(v___x_5367_, v___x_5368_);
if (v___x_5369_ == 0)
{
lean_dec(v_ty_x3f_5366_);
return v_acc_5365_;
}
else
{
uint8_t v___x_5370_; 
v___x_5370_ = lean_nat_dec_le(v___x_5368_, v___x_5368_);
if (v___x_5370_ == 0)
{
if (v___x_5369_ == 0)
{
lean_dec(v_ty_x3f_5366_);
return v_acc_5365_;
}
else
{
size_t v___x_5371_; size_t v___x_5372_; lean_object* v___x_5373_; 
v___x_5371_ = ((size_t)0ULL);
v___x_5372_ = lean_usize_of_nat(v___x_5368_);
v___x_5373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5366_, v_pats_5364_, v___x_5371_, v___x_5372_, v_acc_5365_);
return v___x_5373_;
}
}
else
{
size_t v___x_5374_; size_t v___x_5375_; lean_object* v___x_5376_; 
v___x_5374_ = ((size_t)0ULL);
v___x_5375_ = lean_usize_of_nat(v___x_5368_);
v___x_5376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5366_, v_pats_5364_, v___x_5374_, v___x_5375_, v_acc_5365_);
return v___x_5376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5380_, lean_object* v_acc_5381_, lean_object* v_ty_x3f_5382_){
_start:
{
lean_object* v___x_5383_; uint8_t v___x_5384_; 
v___x_5383_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5380_);
v___x_5384_ = l_Lean_Syntax_isOfKind(v_pat_5380_, v___x_5383_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5380_);
v___x_5386_ = l_Lean_Syntax_isOfKind(v_pat_5380_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_dec(v_ty_x3f_5382_);
lean_dec(v_pat_5380_);
return v_acc_5381_;
}
else
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v___x_5387_ = lean_unsigned_to_nat(1u);
v___x_5388_ = l_Lean_Syntax_getArg(v_pat_5380_, v___x_5387_);
v___x_5389_ = lean_unsigned_to_nat(2u);
v___x_5390_ = l_Lean_Syntax_getArg(v_pat_5380_, v___x_5389_);
lean_dec(v_pat_5380_);
v___x_5391_ = l_Lean_Syntax_isNone(v___x_5390_);
if (v___x_5391_ == 0)
{
uint8_t v___x_5392_; 
lean_dec(v_ty_x3f_5382_);
lean_inc(v___x_5390_);
v___x_5392_ = l_Lean_Syntax_matchesNull(v___x_5390_, v___x_5389_);
if (v___x_5392_ == 0)
{
lean_dec(v___x_5390_);
lean_dec(v___x_5388_);
return v_acc_5381_;
}
else
{
lean_object* v_ty_x3f_x27_5393_; lean_object* v___x_5394_; lean_object* v_pats_5395_; lean_object* v___x_5396_; 
v_ty_x3f_x27_5393_ = l_Lean_Syntax_getArg(v___x_5390_, v___x_5387_);
lean_dec(v___x_5390_);
v___x_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_ty_x3f_x27_5393_);
v_pats_5395_ = l_Lean_Syntax_getArgs(v___x_5388_);
lean_dec(v___x_5388_);
v___x_5396_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5395_, v_acc_5381_, v___x_5394_);
lean_dec_ref(v_pats_5395_);
return v___x_5396_;
}
}
else
{
lean_object* v_pats_5397_; lean_object* v___x_5398_; 
lean_dec(v___x_5390_);
v_pats_5397_ = l_Lean_Syntax_getArgs(v___x_5388_);
lean_dec(v___x_5388_);
v___x_5398_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5397_, v_acc_5381_, v_ty_x3f_5382_);
lean_dec_ref(v_pats_5397_);
return v___x_5398_;
}
}
}
else
{
lean_object* v___x_5399_; lean_object* v_p_5400_; 
v___x_5399_ = lean_unsigned_to_nat(0u);
v_p_5400_ = l_Lean_Syntax_getArg(v_pat_5380_, v___x_5399_);
lean_dec(v_pat_5380_);
if (lean_obj_tag(v_ty_x3f_5382_) == 0)
{
lean_object* v___x_5401_; 
v___x_5401_ = lean_array_push(v_acc_5381_, v_p_5400_);
return v___x_5401_;
}
else
{
lean_object* v_val_5402_; lean_object* v___x_5403_; lean_object* v_ref_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
v_val_5402_ = lean_ctor_get(v_ty_x3f_5382_, 0);
lean_inc(v_val_5402_);
lean_dec_ref_known(v_ty_x3f_5382_, 1);
v___x_5403_ = lean_box(0);
v_ref_5404_ = l_Lean_replaceRef(v_p_5400_, v___x_5403_);
v___x_5405_ = 0;
v___x_5406_ = l_Lean_SourceInfo_fromRef(v_ref_5404_, v___x_5405_);
lean_dec(v_ref_5404_);
v___x_5407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5406_, 7);
v___x_5409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5406_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5411_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5412_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5413_ = l_Lean_Syntax_node1(v___x_5406_, v___x_5412_, v_p_5400_);
v___x_5414_ = l_Lean_Syntax_node1(v___x_5406_, v___x_5411_, v___x_5413_);
v___x_5415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5406_);
lean_ctor_set(v___x_5416_, 1, v___x_5415_);
v___x_5417_ = l_Lean_Syntax_node2(v___x_5406_, v___x_5412_, v___x_5416_, v_val_5402_);
v___x_5418_ = l_Lean_Syntax_node2(v___x_5406_, v___x_5410_, v___x_5414_, v___x_5417_);
v___x_5419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5406_);
lean_ctor_set(v___x_5420_, 1, v___x_5419_);
v___x_5421_ = l_Lean_Syntax_node3(v___x_5406_, v___x_5407_, v___x_5409_, v___x_5418_, v___x_5420_);
v___x_5422_ = lean_array_push(v_acc_5381_, v___x_5421_);
return v___x_5422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5423_, lean_object* v_as_5424_, size_t v_i_5425_, size_t v_stop_5426_, lean_object* v_b_5427_){
_start:
{
uint8_t v___x_5428_; 
v___x_5428_ = lean_usize_dec_eq(v_i_5425_, v_stop_5426_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; lean_object* v___x_5430_; size_t v___x_5431_; size_t v___x_5432_; 
v___x_5429_ = lean_array_uget_borrowed(v_as_5424_, v_i_5425_);
lean_inc(v_ty_x3f_5423_);
lean_inc(v___x_5429_);
v___x_5430_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5429_, v_b_5427_, v_ty_x3f_5423_);
v___x_5431_ = ((size_t)1ULL);
v___x_5432_ = lean_usize_add(v_i_5425_, v___x_5431_);
v_i_5425_ = v___x_5432_;
v_b_5427_ = v___x_5430_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5423_);
return v_b_5427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5434_, lean_object* v_as_5435_, lean_object* v_i_5436_, lean_object* v_stop_5437_, lean_object* v_b_5438_){
_start:
{
size_t v_i_boxed_5439_; size_t v_stop_boxed_5440_; lean_object* v_res_5441_; 
v_i_boxed_5439_ = lean_unbox_usize(v_i_5436_);
lean_dec(v_i_5436_);
v_stop_boxed_5440_ = lean_unbox_usize(v_stop_5437_);
lean_dec(v_stop_5437_);
v_res_5441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5434_, v_as_5435_, v_i_boxed_5439_, v_stop_boxed_5440_, v_b_5438_);
lean_dec_ref(v_as_5435_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5442_, lean_object* v_acc_5443_, lean_object* v_ty_x3f_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5442_, v_acc_5443_, v_ty_x3f_5444_);
lean_dec_ref(v_pats_5442_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5448_, 0, v___x_5447_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5451_, lean_object* v_pats_5452_, lean_object* v_ty_x3f_5453_, lean_object* v_cont_5454_, lean_object* v_i_5455_, lean_object* v_g_5456_, lean_object* v_fs_5457_, lean_object* v_clears_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5451_, v_pats_5452_, v_ty_x3f_5453_, v_cont_5454_, v_i_5455_, v_g_5456_, v_fs_5457_, v_clears_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_a_5460_);
lean_dec(v_i_5455_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5468_ = _args[0];
lean_object* v_ref_5469_ = _args[1];
lean_object* v_pats_5470_ = _args[2];
lean_object* v_ty_x3f_5471_ = _args[3];
lean_object* v_cont_5472_ = _args[4];
lean_object* v_i_5473_ = _args[5];
lean_object* v_g_5474_ = _args[6];
lean_object* v_fs_5475_ = _args[7];
lean_object* v_clears_5476_ = _args[8];
lean_object* v_a_5477_ = _args[9];
lean_object* v_a_5478_ = _args[10];
lean_object* v_a_5479_ = _args[11];
lean_object* v_a_5480_ = _args[12];
lean_object* v_a_5481_ = _args[13];
lean_object* v_a_5482_ = _args[14];
lean_object* v_a_5483_ = _args[15];
lean_object* v_a_5484_ = _args[16];
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5468_, v_ref_5469_, v_pats_5470_, v_ty_x3f_5471_, v_cont_5472_, v_i_5473_, v_g_5474_, v_fs_5475_, v_clears_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
lean_dec(v_a_5483_);
lean_dec_ref(v_a_5482_);
lean_dec(v_a_5481_);
lean_dec_ref(v_a_5480_);
lean_dec(v_a_5479_);
lean_dec_ref(v_a_5478_);
lean_dec(v_i_5473_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5486_, lean_object* v_fs_5487_, lean_object* v_clears_5488_, lean_object* v_ref_5489_, lean_object* v_pats_5490_, lean_object* v_ty_x3f_5491_, lean_object* v_a_5492_, lean_object* v_cont_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_){
_start:
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; 
v___x_5501_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5486_);
v___x_5502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5502_, 0, lean_box(0));
lean_closure_set(v___x_5502_, 1, v_ref_5489_);
lean_closure_set(v___x_5502_, 2, v_pats_5490_);
lean_closure_set(v___x_5502_, 3, v_ty_x3f_5491_);
lean_closure_set(v___x_5502_, 4, v_cont_5493_);
lean_closure_set(v___x_5502_, 5, v___x_5501_);
lean_closure_set(v___x_5502_, 6, v_g_5486_);
lean_closure_set(v___x_5502_, 7, v_fs_5487_);
lean_closure_set(v___x_5502_, 8, v_clears_5488_);
lean_closure_set(v___x_5502_, 9, v_a_5492_);
v___x_5503_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5486_, v___x_5502_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5504_, lean_object* v_fs_5505_, lean_object* v_clears_5506_, lean_object* v_a_5507_, lean_object* v_ref_5508_, lean_object* v_pat_5509_, lean_object* v_ty_x3f_5510_, lean_object* v_cont_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_){
_start:
{
lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___x_5531_; uint8_t v___x_5532_; 
v___x_5531_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5509_);
v___x_5532_ = l_Lean_Syntax_isOfKind(v_pat_5509_, v___x_5531_);
if (v___x_5532_ == 0)
{
lean_object* v___x_5533_; uint8_t v___x_5534_; 
lean_dec(v_ref_5508_);
v___x_5533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5509_);
v___x_5534_ = l_Lean_Syntax_isOfKind(v_pat_5509_, v___x_5533_);
if (v___x_5534_ == 0)
{
lean_object* v___x_5535_; 
lean_dec_ref(v_cont_5511_);
lean_dec(v_ty_x3f_5510_);
lean_dec(v_pat_5509_);
lean_dec(v_a_5507_);
lean_dec_ref(v_clears_5506_);
lean_dec(v_fs_5505_);
lean_dec(v_g_5504_);
v___x_5535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5535_;
}
else
{
lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v_ty_x3f_x27_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___x_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; 
v___x_5536_ = lean_unsigned_to_nat(1u);
v___x_5537_ = l_Lean_Syntax_getArg(v_pat_5509_, v___x_5536_);
v___x_5550_ = lean_unsigned_to_nat(2u);
v___x_5551_ = l_Lean_Syntax_getArg(v_pat_5509_, v___x_5550_);
v___x_5552_ = l_Lean_Syntax_isNone(v___x_5551_);
if (v___x_5552_ == 0)
{
uint8_t v___x_5553_; 
lean_inc(v___x_5551_);
v___x_5553_ = l_Lean_Syntax_matchesNull(v___x_5551_, v___x_5550_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; 
lean_dec(v___x_5551_);
lean_dec(v___x_5537_);
lean_dec_ref(v_cont_5511_);
lean_dec(v_ty_x3f_5510_);
lean_dec(v_pat_5509_);
lean_dec(v_a_5507_);
lean_dec_ref(v_clears_5506_);
lean_dec(v_fs_5505_);
lean_dec(v_g_5504_);
v___x_5554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5554_;
}
else
{
lean_object* v_ty_x3f_x27_5555_; lean_object* v___x_5556_; 
v_ty_x3f_x27_5555_ = l_Lean_Syntax_getArg(v___x_5551_, v___x_5536_);
lean_dec(v___x_5551_);
v___x_5556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5556_, 0, v_ty_x3f_x27_5555_);
v_ty_x3f_x27_5539_ = v___x_5556_;
v___y_5540_ = v_a_5512_;
v___y_5541_ = v_a_5513_;
v___y_5542_ = v_a_5514_;
v___y_5543_ = v_a_5515_;
v___y_5544_ = v_a_5516_;
v___y_5545_ = v_a_5517_;
goto v___jp_5538_;
}
}
else
{
lean_object* v___x_5557_; 
lean_dec(v___x_5551_);
v___x_5557_ = lean_box(0);
v_ty_x3f_x27_5539_ = v___x_5557_;
v___y_5540_ = v_a_5512_;
v___y_5541_ = v_a_5513_;
v___y_5542_ = v_a_5514_;
v___y_5543_ = v_a_5515_;
v___y_5544_ = v_a_5516_;
v___y_5545_ = v_a_5517_;
goto v___jp_5538_;
}
v___jp_5538_:
{
lean_object* v_pats_5546_; lean_object* v___x_5547_; uint8_t v___x_5548_; 
v_pats_5546_ = l_Lean_Syntax_getArgs(v___x_5537_);
lean_dec(v___x_5537_);
v___x_5547_ = lean_array_get_size(v_pats_5546_);
v___x_5548_ = lean_nat_dec_eq(v___x_5547_, v___x_5536_);
if (v___x_5548_ == 0)
{
lean_object* v___x_5549_; 
lean_dec(v_pat_5509_);
v___x_5549_ = lean_box(0);
v___y_5520_ = v___y_5545_;
v___y_5521_ = v___y_5544_;
v___y_5522_ = v___y_5542_;
v___y_5523_ = v_pats_5546_;
v___y_5524_ = v___y_5541_;
v___y_5525_ = v___y_5543_;
v___y_5526_ = v_ty_x3f_x27_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v___x_5549_;
goto v___jp_5519_;
}
else
{
v___y_5520_ = v___y_5545_;
v___y_5521_ = v___y_5544_;
v___y_5522_ = v___y_5542_;
v___y_5523_ = v_pats_5546_;
v___y_5524_ = v___y_5541_;
v___y_5525_ = v___y_5543_;
v___y_5526_ = v_ty_x3f_x27_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v_pat_5509_;
goto v___jp_5519_;
}
}
}
}
else
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
v___x_5558_ = lean_unsigned_to_nat(0u);
v___x_5559_ = l_Lean_Syntax_getArg(v_pat_5509_, v___x_5558_);
lean_dec(v_pat_5509_);
v___x_5560_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5559_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5562_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5599_; lean_object* v_ref_5603_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_a_5561_);
lean_dec_ref_known(v___x_5560_, 1);
v___x_5562_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5508_, v_a_5561_, v_ty_x3f_5510_);
lean_dec(v_ty_x3f_5510_);
v_ref_5603_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_ref_5603_);
v___y_5599_ = v_ref_5603_;
goto v___jp_5598_;
v___jp_5563_:
{
lean_object* v_fileName_5566_; lean_object* v_fileMap_5567_; lean_object* v_options_5568_; lean_object* v_currRecDepth_5569_; lean_object* v_maxRecDepth_5570_; lean_object* v_ref_5571_; lean_object* v_currNamespace_5572_; lean_object* v_openDecls_5573_; lean_object* v_initHeartbeats_5574_; lean_object* v_maxHeartbeats_5575_; lean_object* v_quotContext_5576_; lean_object* v_currMacroScope_5577_; uint8_t v_diag_5578_; lean_object* v_cancelTk_x3f_5579_; uint8_t v_suppressElabErrors_5580_; lean_object* v_inheritedTraceOptions_5581_; lean_object* v_ref_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
v_fileName_5566_ = lean_ctor_get(v_a_5516_, 0);
v_fileMap_5567_ = lean_ctor_get(v_a_5516_, 1);
v_options_5568_ = lean_ctor_get(v_a_5516_, 2);
v_currRecDepth_5569_ = lean_ctor_get(v_a_5516_, 3);
v_maxRecDepth_5570_ = lean_ctor_get(v_a_5516_, 4);
v_ref_5571_ = lean_ctor_get(v_a_5516_, 5);
v_currNamespace_5572_ = lean_ctor_get(v_a_5516_, 6);
v_openDecls_5573_ = lean_ctor_get(v_a_5516_, 7);
v_initHeartbeats_5574_ = lean_ctor_get(v_a_5516_, 8);
v_maxHeartbeats_5575_ = lean_ctor_get(v_a_5516_, 9);
v_quotContext_5576_ = lean_ctor_get(v_a_5516_, 10);
v_currMacroScope_5577_ = lean_ctor_get(v_a_5516_, 11);
v_diag_5578_ = lean_ctor_get_uint8(v_a_5516_, sizeof(void*)*14);
v_cancelTk_x3f_5579_ = lean_ctor_get(v_a_5516_, 12);
v_suppressElabErrors_5580_ = lean_ctor_get_uint8(v_a_5516_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5581_ = lean_ctor_get(v_a_5516_, 13);
v_ref_5582_ = l_Lean_replaceRef(v___y_5564_, v_ref_5571_);
lean_dec(v___y_5564_);
lean_inc_ref(v_inheritedTraceOptions_5581_);
lean_inc(v_cancelTk_x3f_5579_);
lean_inc(v_currMacroScope_5577_);
lean_inc(v_quotContext_5576_);
lean_inc(v_maxHeartbeats_5575_);
lean_inc(v_initHeartbeats_5574_);
lean_inc(v_openDecls_5573_);
lean_inc(v_currNamespace_5572_);
lean_inc(v_maxRecDepth_5570_);
lean_inc(v_currRecDepth_5569_);
lean_inc_ref(v_options_5568_);
lean_inc_ref(v_fileMap_5567_);
lean_inc_ref(v_fileName_5566_);
v___x_5583_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5583_, 0, v_fileName_5566_);
lean_ctor_set(v___x_5583_, 1, v_fileMap_5567_);
lean_ctor_set(v___x_5583_, 2, v_options_5568_);
lean_ctor_set(v___x_5583_, 3, v_currRecDepth_5569_);
lean_ctor_set(v___x_5583_, 4, v_maxRecDepth_5570_);
lean_ctor_set(v___x_5583_, 5, v_ref_5582_);
lean_ctor_set(v___x_5583_, 6, v_currNamespace_5572_);
lean_ctor_set(v___x_5583_, 7, v_openDecls_5573_);
lean_ctor_set(v___x_5583_, 8, v_initHeartbeats_5574_);
lean_ctor_set(v___x_5583_, 9, v_maxHeartbeats_5575_);
lean_ctor_set(v___x_5583_, 10, v_quotContext_5576_);
lean_ctor_set(v___x_5583_, 11, v_currMacroScope_5577_);
lean_ctor_set(v___x_5583_, 12, v_cancelTk_x3f_5579_);
lean_ctor_set(v___x_5583_, 13, v_inheritedTraceOptions_5581_);
lean_ctor_set_uint8(v___x_5583_, sizeof(void*)*14, v_diag_5578_);
lean_ctor_set_uint8(v___x_5583_, sizeof(void*)*14 + 1, v_suppressElabErrors_5580_);
v___x_5584_ = l_Lean_MVarId_intro(v_g_5504_, v___y_5565_, v_a_5514_, v_a_5515_, v___x_5583_, v_a_5517_);
lean_dec_ref_known(v___x_5583_, 14);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v_fst_5586_; lean_object* v_snd_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
lean_inc(v_a_5585_);
lean_dec_ref_known(v___x_5584_, 1);
v_fst_5586_ = lean_ctor_get(v_a_5585_, 0);
lean_inc(v_fst_5586_);
v_snd_5587_ = lean_ctor_get(v_a_5585_, 1);
lean_inc(v_snd_5587_);
lean_dec(v_a_5585_);
v___x_5588_ = l_Lean_Expr_fvar___override(v_fst_5586_);
v___x_5589_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5587_, v_fs_5505_, v_clears_5506_, v___x_5588_, v_a_5507_, v___x_5562_, v_cont_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
lean_dec_ref(v___x_5588_);
return v___x_5589_;
}
else
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
lean_dec_ref(v___x_5562_);
lean_dec_ref(v_cont_5511_);
lean_dec(v_a_5507_);
lean_dec_ref(v_clears_5506_);
lean_dec(v_fs_5505_);
v_a_5590_ = lean_ctor_get(v___x_5584_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5584_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5584_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
v___jp_5598_:
{
lean_object* v___x_5600_; 
v___x_5600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5562_);
if (lean_obj_tag(v___x_5600_) == 0)
{
lean_object* v___x_5601_; 
v___x_5601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5564_ = v___y_5599_;
v___y_5565_ = v___x_5601_;
goto v___jp_5563_;
}
else
{
lean_object* v_val_5602_; 
v_val_5602_ = lean_ctor_get(v___x_5600_, 0);
lean_inc(v_val_5602_);
lean_dec_ref_known(v___x_5600_, 1);
v___y_5564_ = v___y_5599_;
v___y_5565_ = v_val_5602_;
goto v___jp_5563_;
}
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
lean_dec_ref(v_cont_5511_);
lean_dec(v_ty_x3f_5510_);
lean_dec(v_ref_5508_);
lean_dec(v_a_5507_);
lean_dec_ref(v_clears_5506_);
lean_dec(v_fs_5505_);
lean_dec(v_g_5504_);
v_a_5604_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5560_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_a_5604_);
lean_dec(v___x_5560_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
v___jp_5519_:
{
if (lean_obj_tag(v___y_5526_) == 0)
{
lean_object* v___x_5529_; 
v___x_5529_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5504_, v_fs_5505_, v_clears_5506_, v___y_5528_, v___y_5523_, v_ty_x3f_5510_, v_a_5507_, v_cont_5511_, v___y_5527_, v___y_5524_, v___y_5522_, v___y_5525_, v___y_5521_, v___y_5520_);
return v___x_5529_;
}
else
{
lean_object* v___x_5530_; 
lean_dec(v_ty_x3f_5510_);
v___x_5530_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5504_, v_fs_5505_, v_clears_5506_, v___y_5528_, v___y_5523_, v___y_5526_, v_a_5507_, v_cont_5511_, v___y_5527_, v___y_5524_, v___y_5522_, v___y_5525_, v___y_5521_, v___y_5520_);
return v___x_5530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5612_, lean_object* v_pats_5613_, lean_object* v_ty_x3f_5614_, lean_object* v_cont_5615_, lean_object* v_i_5616_, lean_object* v_g_5617_, lean_object* v_fs_5618_, lean_object* v_clears_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_){
_start:
{
lean_object* v___x_5628_; uint8_t v___x_5629_; 
v___x_5628_ = lean_array_get_size(v_pats_5613_);
v___x_5629_ = lean_nat_dec_lt(v_i_5616_, v___x_5628_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; 
lean_dec(v_ty_x3f_5614_);
lean_dec_ref(v_pats_5613_);
lean_dec(v_ref_5612_);
lean_inc(v_a_5626_);
lean_inc_ref(v_a_5625_);
lean_inc(v_a_5624_);
lean_inc_ref(v_a_5623_);
lean_inc(v_a_5622_);
lean_inc_ref(v_a_5621_);
v___x_5630_ = lean_apply_11(v_cont_5615_, v_g_5617_, v_fs_5618_, v_clears_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, lean_box(0));
return v___x_5630_;
}
else
{
lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5631_ = lean_array_fget(v_pats_5613_, v_i_5616_);
v___x_5632_ = lean_unsigned_to_nat(1u);
v___x_5633_ = lean_nat_add(v_i_5616_, v___x_5632_);
lean_inc(v_ty_x3f_5614_);
lean_inc(v_ref_5612_);
v___x_5634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5634_, 0, v_ref_5612_);
lean_closure_set(v___x_5634_, 1, v_pats_5613_);
lean_closure_set(v___x_5634_, 2, v_ty_x3f_5614_);
lean_closure_set(v___x_5634_, 3, v_cont_5615_);
lean_closure_set(v___x_5634_, 4, v___x_5633_);
v___x_5635_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5617_, v_fs_5618_, v_clears_5619_, v_a_5620_, v_ref_5612_, v___x_5631_, v_ty_x3f_5614_, v___x_5634_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_);
return v___x_5635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5636_, lean_object* v_ref_5637_, lean_object* v_pats_5638_, lean_object* v_ty_x3f_5639_, lean_object* v_cont_5640_, lean_object* v_i_5641_, lean_object* v_g_5642_, lean_object* v_fs_5643_, lean_object* v_clears_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v___x_5653_; 
v___x_5653_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5637_, v_pats_5638_, v_ty_x3f_5639_, v_cont_5640_, v_i_5641_, v_g_5642_, v_fs_5643_, v_clears_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5654_, lean_object* v_fs_5655_, lean_object* v_clears_5656_, lean_object* v_ref_5657_, lean_object* v_pats_5658_, lean_object* v_ty_x3f_5659_, lean_object* v_a_5660_, lean_object* v_cont_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5654_, v_fs_5655_, v_clears_5656_, v_ref_5657_, v_pats_5658_, v_ty_x3f_5659_, v_a_5660_, v_cont_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_);
lean_dec(v_a_5667_);
lean_dec_ref(v_a_5666_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5670_, lean_object* v_fs_5671_, lean_object* v_clears_5672_, lean_object* v_a_5673_, lean_object* v_ref_5674_, lean_object* v_pat_5675_, lean_object* v_ty_x3f_5676_, lean_object* v_cont_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5670_, v_fs_5671_, v_clears_5672_, v_a_5673_, v_ref_5674_, v_pat_5675_, v_ty_x3f_5676_, v_cont_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
lean_object* v_res_5703_; 
v_res_5703_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
return v_res_5703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5704_, lean_object* v_g_5705_, lean_object* v_fs_5706_, lean_object* v_clears_5707_, lean_object* v_a_5708_, lean_object* v_ref_5709_, lean_object* v_pat_5710_, lean_object* v_ty_x3f_5711_, lean_object* v_cont_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_){
_start:
{
lean_object* v___x_5720_; 
v___x_5720_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5705_, v_fs_5706_, v_clears_5707_, v_a_5708_, v_ref_5709_, v_pat_5710_, v_ty_x3f_5711_, v_cont_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_);
return v___x_5720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5721_, lean_object* v_g_5722_, lean_object* v_fs_5723_, lean_object* v_clears_5724_, lean_object* v_a_5725_, lean_object* v_ref_5726_, lean_object* v_pat_5727_, lean_object* v_ty_x3f_5728_, lean_object* v_cont_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_){
_start:
{
lean_object* v_res_5737_; 
v_res_5737_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5721_, v_g_5722_, v_fs_5723_, v_clears_5724_, v_a_5725_, v_ref_5726_, v_pat_5727_, v_ty_x3f_5728_, v_cont_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
return v_res_5737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5738_, lean_object* v_g_5739_, lean_object* v_fs_5740_, lean_object* v_clears_5741_, lean_object* v_ref_5742_, lean_object* v_pats_5743_, lean_object* v_ty_x3f_5744_, lean_object* v_a_5745_, lean_object* v_cont_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_){
_start:
{
lean_object* v___x_5754_; 
v___x_5754_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5739_, v_fs_5740_, v_clears_5741_, v_ref_5742_, v_pats_5743_, v_ty_x3f_5744_, v_a_5745_, v_cont_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_);
return v___x_5754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5755_, lean_object* v_g_5756_, lean_object* v_fs_5757_, lean_object* v_clears_5758_, lean_object* v_ref_5759_, lean_object* v_pats_5760_, lean_object* v_ty_x3f_5761_, lean_object* v_a_5762_, lean_object* v_cont_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5755_, v_g_5756_, v_fs_5757_, v_clears_5758_, v_ref_5759_, v_pats_5760_, v_ty_x3f_5761_, v_a_5762_, v_cont_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_);
lean_dec(v_a_5769_);
lean_dec_ref(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
lean_dec(v_a_5765_);
lean_dec_ref(v_a_5764_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5772_, lean_object* v___x_5773_, lean_object* v___x_5774_, lean_object* v___x_5775_, lean_object* v_pats_5776_, lean_object* v_ty_x3f_5777_, lean_object* v___x_5778_, lean_object* v___x_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_){
_start:
{
lean_object* v___x_5787_; 
v___x_5787_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5772_, v___x_5773_, v___x_5774_, v___x_5775_, v_pats_5776_, v_ty_x3f_5777_, v___x_5778_, v___x_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v_a_5788_; lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5796_; 
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5790_ = v___x_5787_;
v_isShared_5791_ = v_isSharedCheck_5796_;
goto v_resetjp_5789_;
}
else
{
lean_inc(v_a_5788_);
lean_dec(v___x_5787_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5796_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
lean_object* v___x_5792_; lean_object* v___x_5794_; 
v___x_5792_ = lean_array_to_list(v_a_5788_);
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 0, v___x_5792_);
v___x_5794_ = v___x_5790_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5792_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
else
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
v_a_5797_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5787_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5787_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5805_, lean_object* v___x_5806_, lean_object* v___x_5807_, lean_object* v___x_5808_, lean_object* v_pats_5809_, lean_object* v_ty_x3f_5810_, lean_object* v___x_5811_, lean_object* v___x_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5805_, v___x_5806_, v___x_5807_, v___x_5808_, v_pats_5809_, v_ty_x3f_5810_, v___x_5811_, v___x_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
return v_res_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5821_, lean_object* v_ty_x3f_5822_, lean_object* v_g_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___f_5835_; uint8_t v___x_5836_; lean_object* v___x_5837_; 
v___x_5831_ = lean_box(0);
v___x_5832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5833_ = lean_box(0);
v___x_5834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5835_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5835_, 0, v_g_5823_);
lean_closure_set(v___f_5835_, 1, v___x_5831_);
lean_closure_set(v___f_5835_, 2, v___x_5832_);
lean_closure_set(v___f_5835_, 3, v___x_5833_);
lean_closure_set(v___f_5835_, 4, v_pats_5821_);
lean_closure_set(v___f_5835_, 5, v_ty_x3f_5822_);
lean_closure_set(v___f_5835_, 6, v___x_5832_);
lean_closure_set(v___f_5835_, 7, v___x_5834_);
v___x_5836_ = 1;
v___x_5837_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5835_, v___x_5836_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5838_, lean_object* v_ty_x3f_5839_, lean_object* v_g_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5838_, v_ty_x3f_5839_, v_g_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_);
lean_dec(v_a_5846_);
lean_dec_ref(v_a_5845_);
lean_dec(v_a_5844_);
lean_dec_ref(v_a_5843_);
lean_dec(v_a_5842_);
lean_dec_ref(v_a_5841_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5850_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5852_){
_start:
{
lean_object* v_res_5853_; 
v_res_5853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_){
_start:
{
lean_object* v_res_5875_; 
v_res_5875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
return v_res_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
lean_object* v___x_5886_; 
lean_inc(v___y_5880_);
lean_inc_ref(v___y_5879_);
lean_inc(v___y_5878_);
lean_inc_ref(v___y_5877_);
v___x_5886_ = lean_apply_9(v_x_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, lean_box(0));
return v___x_5886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
lean_object* v_res_5897_; 
v_res_5897_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
return v_res_5897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5898_, lean_object* v_x_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
lean_object* v___f_5909_; lean_object* v___x_5910_; 
lean_inc(v___y_5903_);
lean_inc_ref(v___y_5902_);
lean_inc(v___y_5901_);
lean_inc_ref(v___y_5900_);
v___f_5909_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5909_, 0, v_x_5899_);
lean_closure_set(v___f_5909_, 1, v___y_5900_);
lean_closure_set(v___f_5909_, 2, v___y_5901_);
lean_closure_set(v___f_5909_, 3, v___y_5902_);
lean_closure_set(v___f_5909_, 4, v___y_5903_);
v___x_5910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5898_, v___f_5909_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
if (lean_obj_tag(v___x_5910_) == 0)
{
return v___x_5910_;
}
else
{
lean_object* v_a_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5918_; 
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v___x_5910_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5913_ = v___x_5910_;
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_a_5911_);
lean_dec(v___x_5910_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___x_5916_; 
if (v_isShared_5914_ == 0)
{
v___x_5916_ = v___x_5913_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
v___x_5916_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
return v___x_5916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5919_, lean_object* v_x_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_){
_start:
{
lean_object* v_res_5930_; 
v_res_5930_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5919_, v_x_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec(v___y_5922_);
lean_dec_ref(v___y_5921_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5931_, lean_object* v_mvarId_5932_, lean_object* v_x_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_){
_start:
{
lean_object* v___x_5943_; 
v___x_5943_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5932_, v_x_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5944_, lean_object* v_mvarId_5945_, lean_object* v_x_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_){
_start:
{
lean_object* v_res_5956_; 
v_res_5956_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5944_, v_mvarId_5945_, v_x_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
lean_dec(v___y_5954_);
lean_dec_ref(v___y_5953_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
return v_res_5956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5957_, lean_object* v_pat_5958_, lean_object* v_a_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_){
_start:
{
lean_object* v___x_5969_; 
v___x_5969_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5957_, v_pat_5958_, v_a_5959_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_a_5970_; lean_object* v___x_5971_; 
v_a_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5970_);
lean_dec_ref_known(v___x_5969_, 1);
v___x_5971_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5970_, v___y_5961_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
return v___x_5971_;
}
else
{
lean_object* v_a_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5979_; 
v_a_5972_ = lean_ctor_get(v___x_5969_, 0);
v_isSharedCheck_5979_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_5979_ == 0)
{
v___x_5974_ = v___x_5969_;
v_isShared_5975_ = v_isSharedCheck_5979_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_a_5972_);
lean_dec(v___x_5969_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5979_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v___x_5977_; 
if (v_isShared_5975_ == 0)
{
v___x_5977_ = v___x_5974_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_a_5972_);
v___x_5977_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
return v___x_5977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5980_, lean_object* v_pat_5981_, lean_object* v_a_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_){
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5980_, v_pat_5981_, v_a_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_);
lean_dec(v___y_5990_);
lean_dec_ref(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec(v___y_5986_);
lean_dec_ref(v___y_5985_);
lean_dec(v___y_5984_);
lean_dec_ref(v___y_5983_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5993_, size_t v_i_5994_, lean_object* v_bs_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_){
_start:
{
uint8_t v___x_6000_; 
v___x_6000_ = lean_usize_dec_lt(v_i_5994_, v_sz_5993_);
if (v___x_6000_ == 0)
{
lean_object* v___x_6001_; 
v___x_6001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6001_, 0, v_bs_5995_);
return v___x_6001_;
}
else
{
lean_object* v_v_6002_; lean_object* v___x_6003_; 
v_v_6002_ = lean_array_uget_borrowed(v_bs_5995_, v_i_5994_);
lean_inc(v_v_6002_);
v___x_6003_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_6002_, v___y_5996_, v___y_5997_, v___y_5998_);
if (lean_obj_tag(v___x_6003_) == 0)
{
lean_object* v_a_6004_; lean_object* v_hIdent_x3f_6005_; lean_object* v_term_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6019_; 
v_a_6004_ = lean_ctor_get(v___x_6003_, 0);
lean_inc(v_a_6004_);
lean_dec_ref_known(v___x_6003_, 1);
v_hIdent_x3f_6005_ = lean_ctor_get(v_a_6004_, 0);
v_term_6006_ = lean_ctor_get(v_a_6004_, 1);
v_isSharedCheck_6019_ = !lean_is_exclusive(v_a_6004_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_6008_ = v_a_6004_;
v_isShared_6009_ = v_isSharedCheck_6019_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_term_6006_);
lean_inc(v_hIdent_x3f_6005_);
lean_dec(v_a_6004_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6019_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6010_; lean_object* v_bs_x27_6011_; lean_object* v___x_6013_; 
v___x_6010_ = lean_unsigned_to_nat(0u);
v_bs_x27_6011_ = lean_array_uset(v_bs_5995_, v_i_5994_, v___x_6010_);
if (v_isShared_6009_ == 0)
{
v___x_6013_ = v___x_6008_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_hIdent_x3f_6005_);
lean_ctor_set(v_reuseFailAlloc_6018_, 1, v_term_6006_);
v___x_6013_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
size_t v___x_6014_; size_t v___x_6015_; lean_object* v___x_6016_; 
v___x_6014_ = ((size_t)1ULL);
v___x_6015_ = lean_usize_add(v_i_5994_, v___x_6014_);
v___x_6016_ = lean_array_uset(v_bs_x27_6011_, v_i_5994_, v___x_6013_);
v_i_5994_ = v___x_6015_;
v_bs_5995_ = v___x_6016_;
goto _start;
}
}
}
else
{
lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec_ref(v_bs_5995_);
v_a_6020_ = lean_ctor_get(v___x_6003_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_6003_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_6003_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_6003_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_6028_, lean_object* v_i_6029_, lean_object* v_bs_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_){
_start:
{
size_t v_sz_boxed_6035_; size_t v_i_boxed_6036_; lean_object* v_res_6037_; 
v_sz_boxed_6035_ = lean_unbox_usize(v_sz_6028_);
lean_dec(v_sz_6028_);
v_i_boxed_6036_ = lean_unbox_usize(v_i_6029_);
lean_dec(v_i_6029_);
v_res_6037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_6035_, v_i_boxed_6036_, v_bs_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec_ref(v___y_6031_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_){
_start:
{
lean_object* v___y_6055_; lean_object* v_pat_6056_; lean_object* v___y_6057_; lean_object* v___y_6058_; lean_object* v___y_6059_; lean_object* v___y_6060_; lean_object* v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6064_; lean_object* v___x_6090_; uint8_t v___x_6091_; 
v___x_6090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_6044_);
v___x_6091_ = l_Lean_Syntax_isOfKind(v_stx_6044_, v___x_6090_);
if (v___x_6091_ == 0)
{
lean_object* v___x_6092_; 
lean_dec(v_stx_6044_);
v___x_6092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6092_;
}
else
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; uint8_t v___x_6097_; 
v___x_6093_ = lean_unsigned_to_nat(1u);
v___x_6094_ = l_Lean_Syntax_getArg(v_stx_6044_, v___x_6093_);
v___x_6095_ = lean_unsigned_to_nat(2u);
v___x_6096_ = l_Lean_Syntax_getArg(v_stx_6044_, v___x_6095_);
v___x_6097_ = l_Lean_Syntax_isNone(v___x_6096_);
if (v___x_6097_ == 0)
{
uint8_t v___x_6098_; 
lean_dec(v_stx_6044_);
lean_inc(v___x_6096_);
v___x_6098_ = l_Lean_Syntax_matchesNull(v___x_6096_, v___x_6095_);
if (v___x_6098_ == 0)
{
lean_object* v___x_6099_; 
lean_dec(v___x_6096_);
lean_dec(v___x_6094_);
v___x_6099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6099_;
}
else
{
lean_object* v_pat_x3f_6100_; lean_object* v___x_6101_; 
v_pat_x3f_6100_ = l_Lean_Syntax_getArg(v___x_6096_, v___x_6093_);
lean_dec(v___x_6096_);
v___x_6101_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6100_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_);
if (lean_obj_tag(v___x_6101_) == 0)
{
lean_object* v_a_6102_; lean_object* v_tgts_6103_; 
v_a_6102_ = lean_ctor_get(v___x_6101_, 0);
lean_inc(v_a_6102_);
lean_dec_ref_known(v___x_6101_, 1);
v_tgts_6103_ = l_Lean_Syntax_getArgs(v___x_6094_);
lean_dec(v___x_6094_);
v___y_6055_ = v_tgts_6103_;
v_pat_6056_ = v_a_6102_;
v___y_6057_ = v_a_6045_;
v___y_6058_ = v_a_6046_;
v___y_6059_ = v_a_6047_;
v___y_6060_ = v_a_6048_;
v___y_6061_ = v_a_6049_;
v___y_6062_ = v_a_6050_;
v___y_6063_ = v_a_6051_;
v___y_6064_ = v_a_6052_;
goto v___jp_6054_;
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
lean_dec(v___x_6094_);
v_a_6104_ = lean_ctor_get(v___x_6101_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6101_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6101_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6101_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
}
}
else
{
lean_object* v___x_6112_; lean_object* v_tk_6113_; lean_object* v_tgts_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
lean_dec(v___x_6096_);
v___x_6112_ = lean_unsigned_to_nat(0u);
v_tk_6113_ = l_Lean_Syntax_getArg(v_stx_6044_, v___x_6112_);
lean_dec(v_stx_6044_);
v_tgts_6114_ = l_Lean_Syntax_getArgs(v___x_6094_);
lean_dec(v___x_6094_);
v___x_6115_ = lean_box(0);
v___x_6116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6116_, 0, v_tk_6113_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___y_6055_ = v_tgts_6114_;
v_pat_6056_ = v___x_6116_;
v___y_6057_ = v_a_6045_;
v___y_6058_ = v_a_6046_;
v___y_6059_ = v_a_6047_;
v___y_6060_ = v_a_6048_;
v___y_6061_ = v_a_6049_;
v___y_6062_ = v_a_6050_;
v___y_6063_ = v_a_6051_;
v___y_6064_ = v_a_6052_;
goto v___jp_6054_;
}
}
v___jp_6054_:
{
lean_object* v___x_6065_; size_t v_sz_6066_; size_t v___x_6067_; lean_object* v___x_6068_; 
v___x_6065_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6055_);
lean_dec_ref(v___y_6055_);
v_sz_6066_ = lean_array_size(v___x_6065_);
v___x_6067_ = ((size_t)0ULL);
v___x_6068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6066_, v___x_6067_, v___x_6065_, v___y_6061_, v___y_6063_, v___y_6064_);
if (lean_obj_tag(v___x_6068_) == 0)
{
lean_object* v_a_6069_; lean_object* v___x_6070_; 
v_a_6069_ = lean_ctor_get(v___x_6068_, 0);
lean_inc(v_a_6069_);
lean_dec_ref_known(v___x_6068_, 1);
v___x_6070_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6058_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v_a_6071_; lean_object* v___f_6072_; lean_object* v___x_6073_; 
v_a_6071_ = lean_ctor_get(v___x_6070_, 0);
lean_inc_n(v_a_6071_, 2);
lean_dec_ref_known(v___x_6070_, 1);
v___f_6072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6072_, 0, v_a_6069_);
lean_closure_set(v___f_6072_, 1, v_pat_6056_);
lean_closure_set(v___f_6072_, 2, v_a_6071_);
v___x_6073_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6071_, v___f_6072_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_);
return v___x_6073_;
}
else
{
lean_object* v_a_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6081_; 
lean_dec(v_a_6069_);
lean_dec_ref(v_pat_6056_);
v_a_6074_ = lean_ctor_get(v___x_6070_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6070_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6076_ = v___x_6070_;
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_a_6074_);
lean_dec(v___x_6070_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6079_; 
if (v_isShared_6077_ == 0)
{
v___x_6079_ = v___x_6076_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
else
{
lean_object* v_a_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6089_; 
lean_dec_ref(v_pat_6056_);
v_a_6082_ = lean_ctor_get(v___x_6068_, 0);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6068_);
if (v_isSharedCheck_6089_ == 0)
{
v___x_6084_ = v___x_6068_;
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_a_6082_);
lean_dec(v___x_6068_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6087_; 
if (v_isShared_6085_ == 0)
{
v___x_6087_ = v___x_6084_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
v___x_6087_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
return v___x_6087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_, lean_object* v_a_6126_){
_start:
{
lean_object* v_res_6127_; 
v_res_6127_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6117_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_, v_a_6124_, v_a_6125_);
lean_dec(v_a_6125_);
lean_dec_ref(v_a_6124_);
lean_dec(v_a_6123_);
lean_dec_ref(v_a_6122_);
lean_dec(v_a_6121_);
lean_dec_ref(v_a_6120_);
lean_dec(v_a_6119_);
lean_dec_ref(v_a_6118_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6128_, size_t v_i_6129_, lean_object* v_bs_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_){
_start:
{
lean_object* v___x_6140_; 
v___x_6140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6128_, v_i_6129_, v_bs_6130_, v___y_6135_, v___y_6137_, v___y_6138_);
return v___x_6140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6141_, lean_object* v_i_6142_, lean_object* v_bs_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
size_t v_sz_boxed_6153_; size_t v_i_boxed_6154_; lean_object* v_res_6155_; 
v_sz_boxed_6153_ = lean_unbox_usize(v_sz_6141_);
lean_dec(v_sz_6141_);
v_i_boxed_6154_ = lean_unbox_usize(v_i_6142_);
lean_dec(v_i_6142_);
v_res_6155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6153_, v_i_boxed_6154_, v_bs_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
lean_dec(v___y_6151_);
lean_dec_ref(v___y_6150_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6192_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6195_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6196_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6192_, v___x_6193_, v___x_6194_, v___x_6195_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6199_, lean_object* v___x_6200_, lean_object* v_a_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6199_, v___x_6200_, v_a_6201_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
if (lean_obj_tag(v___x_6211_) == 0)
{
lean_object* v_a_6212_; lean_object* v___x_6213_; 
v_a_6212_ = lean_ctor_get(v___x_6211_, 0);
lean_inc(v_a_6212_);
lean_dec_ref_known(v___x_6211_, 1);
v___x_6213_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6212_, v___y_6203_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
return v___x_6213_;
}
else
{
lean_object* v_a_6214_; lean_object* v___x_6216_; uint8_t v_isShared_6217_; uint8_t v_isSharedCheck_6221_; 
v_a_6214_ = lean_ctor_get(v___x_6211_, 0);
v_isSharedCheck_6221_ = !lean_is_exclusive(v___x_6211_);
if (v_isSharedCheck_6221_ == 0)
{
v___x_6216_ = v___x_6211_;
v_isShared_6217_ = v_isSharedCheck_6221_;
goto v_resetjp_6215_;
}
else
{
lean_inc(v_a_6214_);
lean_dec(v___x_6211_);
v___x_6216_ = lean_box(0);
v_isShared_6217_ = v_isSharedCheck_6221_;
goto v_resetjp_6215_;
}
v_resetjp_6215_:
{
lean_object* v___x_6219_; 
if (v_isShared_6217_ == 0)
{
v___x_6219_ = v___x_6216_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_a_6214_);
v___x_6219_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
return v___x_6219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6222_, lean_object* v___x_6223_, lean_object* v_a_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6222_, v___x_6223_, v_a_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6235_, lean_object* v_val_6236_, lean_object* v_a_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6235_, v_val_6236_, v_a_6237_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
if (lean_obj_tag(v___x_6247_) == 0)
{
lean_object* v_a_6248_; lean_object* v___x_6249_; 
v_a_6248_ = lean_ctor_get(v___x_6247_, 0);
lean_inc(v_a_6248_);
lean_dec_ref_known(v___x_6247_, 1);
v___x_6249_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6248_, v___y_6239_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
return v___x_6249_;
}
else
{
lean_object* v_a_6250_; lean_object* v___x_6252_; uint8_t v_isShared_6253_; uint8_t v_isSharedCheck_6257_; 
v_a_6250_ = lean_ctor_get(v___x_6247_, 0);
v_isSharedCheck_6257_ = !lean_is_exclusive(v___x_6247_);
if (v_isSharedCheck_6257_ == 0)
{
v___x_6252_ = v___x_6247_;
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
else
{
lean_inc(v_a_6250_);
lean_dec(v___x_6247_);
v___x_6252_ = lean_box(0);
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
v_resetjp_6251_:
{
lean_object* v___x_6255_; 
if (v_isShared_6253_ == 0)
{
v___x_6255_ = v___x_6252_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_a_6250_);
v___x_6255_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6254_;
}
v_reusejp_6254_:
{
return v___x_6255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6258_, lean_object* v_val_6259_, lean_object* v_a_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_){
_start:
{
lean_object* v_res_6270_; 
v_res_6270_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6258_, v_val_6259_, v_a_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
lean_dec(v___y_6262_);
lean_dec_ref(v___y_6261_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v_ref_6277_; lean_object* v___x_6278_; lean_object* v_a_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6287_; 
v_ref_6277_ = lean_ctor_get(v___y_6274_, 5);
v___x_6278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
v_a_6279_ = lean_ctor_get(v___x_6278_, 0);
v_isSharedCheck_6287_ = !lean_is_exclusive(v___x_6278_);
if (v_isSharedCheck_6287_ == 0)
{
v___x_6281_ = v___x_6278_;
v_isShared_6282_ = v_isSharedCheck_6287_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_a_6279_);
lean_dec(v___x_6278_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6287_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6283_; lean_object* v___x_6285_; 
lean_inc(v_ref_6277_);
v___x_6283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6283_, 0, v_ref_6277_);
lean_ctor_set(v___x_6283_, 1, v_a_6279_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set_tag(v___x_6281_, 1);
lean_ctor_set(v___x_6281_, 0, v___x_6283_);
v___x_6285_ = v___x_6281_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v___x_6283_);
v___x_6285_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
return v___x_6285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
lean_object* v_res_6294_; 
v_res_6294_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
lean_dec(v___y_6292_);
lean_dec_ref(v___y_6291_);
lean_dec(v___y_6290_);
lean_dec_ref(v___y_6289_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6295_, size_t v_i_6296_, lean_object* v_bs_6297_){
_start:
{
uint8_t v___x_6298_; 
v___x_6298_ = lean_usize_dec_lt(v_i_6296_, v_sz_6295_);
if (v___x_6298_ == 0)
{
return v_bs_6297_;
}
else
{
lean_object* v_v_6299_; lean_object* v___x_6300_; lean_object* v_bs_x27_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; size_t v___x_6304_; size_t v___x_6305_; lean_object* v___x_6306_; 
v_v_6299_ = lean_array_uget(v_bs_6297_, v_i_6296_);
v___x_6300_ = lean_unsigned_to_nat(0u);
v_bs_x27_6301_ = lean_array_uset(v_bs_6297_, v_i_6296_, v___x_6300_);
v___x_6302_ = lean_box(0);
v___x_6303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6303_, 0, v___x_6302_);
lean_ctor_set(v___x_6303_, 1, v_v_6299_);
v___x_6304_ = ((size_t)1ULL);
v___x_6305_ = lean_usize_add(v_i_6296_, v___x_6304_);
v___x_6306_ = lean_array_uset(v_bs_x27_6301_, v_i_6296_, v___x_6303_);
v_i_6296_ = v___x_6305_;
v_bs_6297_ = v___x_6306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6308_, lean_object* v_i_6309_, lean_object* v_bs_6310_){
_start:
{
size_t v_sz_boxed_6311_; size_t v_i_boxed_6312_; lean_object* v_res_6313_; 
v_sz_boxed_6311_ = lean_unbox_usize(v_sz_6308_);
lean_dec(v_sz_6308_);
v_i_boxed_6312_ = lean_unbox_usize(v_i_6309_);
lean_dec(v_i_6309_);
v_res_6313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6311_, v_i_boxed_6312_, v_bs_6310_);
return v_res_6313_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6325_ = l_Lean_stringToMessageData(v___x_6324_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_, lean_object* v_a_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_){
_start:
{
lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___x_6359_; uint8_t v___x_6360_; 
v___x_6359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6326_);
v___x_6360_ = l_Lean_Syntax_isOfKind(v_stx_6326_, v___x_6359_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; 
lean_dec(v_stx_6326_);
v___x_6361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6361_;
}
else
{
lean_object* v___x_6362_; lean_object* v_tk_6363_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; lean_object* v___y_6394_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v_a_6404_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v_val_x3f_6420_; lean_object* v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v___y_6427_; lean_object* v___y_6428_; lean_object* v___x_6448_; lean_object* v___y_6450_; lean_object* v___y_6451_; lean_object* v_ty_x3f_6452_; lean_object* v___y_6453_; lean_object* v___y_6454_; lean_object* v___y_6455_; lean_object* v___y_6456_; lean_object* v___y_6457_; lean_object* v___y_6458_; lean_object* v___y_6459_; lean_object* v___y_6460_; lean_object* v_pat_x3f_6471_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; lean_object* v___y_6475_; lean_object* v___y_6476_; lean_object* v___y_6477_; lean_object* v___y_6478_; lean_object* v___y_6479_; lean_object* v___x_6488_; uint8_t v___x_6489_; 
v___x_6362_ = lean_unsigned_to_nat(0u);
v_tk_6363_ = l_Lean_Syntax_getArg(v_stx_6326_, v___x_6362_);
v___x_6448_ = lean_unsigned_to_nat(1u);
v___x_6488_ = l_Lean_Syntax_getArg(v_stx_6326_, v___x_6448_);
v___x_6489_ = l_Lean_Syntax_isNone(v___x_6488_);
if (v___x_6489_ == 0)
{
uint8_t v___x_6490_; 
lean_inc(v___x_6488_);
v___x_6490_ = l_Lean_Syntax_matchesNull(v___x_6488_, v___x_6448_);
if (v___x_6490_ == 0)
{
lean_object* v___x_6491_; 
lean_dec(v___x_6488_);
lean_dec(v_tk_6363_);
lean_dec(v_stx_6326_);
v___x_6491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6491_;
}
else
{
lean_object* v_pat_x3f_6492_; lean_object* v___x_6493_; uint8_t v___x_6494_; 
v_pat_x3f_6492_ = l_Lean_Syntax_getArg(v___x_6488_, v___x_6362_);
lean_dec(v___x_6488_);
v___x_6493_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6492_);
v___x_6494_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6492_, v___x_6493_);
if (v___x_6494_ == 0)
{
lean_object* v___x_6495_; 
lean_dec(v_pat_x3f_6492_);
lean_dec(v_tk_6363_);
lean_dec(v_stx_6326_);
v___x_6495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6495_;
}
else
{
lean_object* v___x_6496_; 
v___x_6496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6496_, 0, v_pat_x3f_6492_);
v_pat_x3f_6471_ = v___x_6496_;
v___y_6472_ = v_a_6327_;
v___y_6473_ = v_a_6328_;
v___y_6474_ = v_a_6329_;
v___y_6475_ = v_a_6330_;
v___y_6476_ = v_a_6331_;
v___y_6477_ = v_a_6332_;
v___y_6478_ = v_a_6333_;
v___y_6479_ = v_a_6334_;
goto v___jp_6470_;
}
}
}
else
{
lean_object* v___x_6497_; 
lean_dec(v___x_6488_);
v___x_6497_ = lean_box(0);
v_pat_x3f_6471_ = v___x_6497_;
v___y_6472_ = v_a_6327_;
v___y_6473_ = v_a_6328_;
v___y_6474_ = v_a_6329_;
v___y_6475_ = v_a_6330_;
v___y_6476_ = v_a_6331_;
v___y_6477_ = v_a_6332_;
v___y_6478_ = v_a_6333_;
v___y_6479_ = v_a_6334_;
goto v___jp_6470_;
}
v___jp_6364_:
{
lean_object* v___x_6376_; 
v___x_6376_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6373_, v___y_6368_, v___y_6374_, v___y_6369_, v___y_6372_);
if (lean_obj_tag(v___x_6376_) == 0)
{
lean_object* v_a_6377_; lean_object* v___x_6378_; size_t v_sz_6379_; lean_object* v___x_6380_; size_t v___x_6381_; lean_object* v___x_6382_; lean_object* v___f_6383_; lean_object* v___x_6384_; 
v_a_6377_ = lean_ctor_get(v___x_6376_, 0);
lean_inc_n(v_a_6377_, 2);
lean_dec_ref_known(v___x_6376_, 1);
v___x_6378_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6367_);
lean_dec_ref(v___y_6367_);
v_sz_6379_ = lean_array_size(v___x_6378_);
v___x_6380_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6363_, v___y_6375_, v___y_6366_);
lean_dec(v___y_6366_);
v___x_6381_ = ((size_t)0ULL);
v___x_6382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6379_, v___x_6381_, v___x_6378_);
v___f_6383_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6383_, 0, v___x_6382_);
lean_closure_set(v___f_6383_, 1, v___x_6380_);
lean_closure_set(v___f_6383_, 2, v_a_6377_);
v___x_6384_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6377_, v___f_6383_, v___y_6371_, v___y_6373_, v___y_6365_, v___y_6370_, v___y_6368_, v___y_6374_, v___y_6369_, v___y_6372_);
return v___x_6384_;
}
else
{
lean_object* v_a_6385_; lean_object* v___x_6387_; uint8_t v_isShared_6388_; uint8_t v_isSharedCheck_6392_; 
lean_dec_ref(v___y_6375_);
lean_dec_ref(v___y_6367_);
lean_dec(v___y_6366_);
lean_dec(v_tk_6363_);
v_a_6385_ = lean_ctor_get(v___x_6376_, 0);
v_isSharedCheck_6392_ = !lean_is_exclusive(v___x_6376_);
if (v_isSharedCheck_6392_ == 0)
{
v___x_6387_ = v___x_6376_;
v_isShared_6388_ = v_isSharedCheck_6392_;
goto v_resetjp_6386_;
}
else
{
lean_inc(v_a_6385_);
lean_dec(v___x_6376_);
v___x_6387_ = lean_box(0);
v_isShared_6388_ = v_isSharedCheck_6392_;
goto v_resetjp_6386_;
}
v_resetjp_6386_:
{
lean_object* v___x_6390_; 
if (v_isShared_6388_ == 0)
{
v___x_6390_ = v___x_6387_;
goto v_reusejp_6389_;
}
else
{
lean_object* v_reuseFailAlloc_6391_; 
v_reuseFailAlloc_6391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6391_, 0, v_a_6385_);
v___x_6390_ = v_reuseFailAlloc_6391_;
goto v_reusejp_6389_;
}
v_reusejp_6389_:
{
return v___x_6390_;
}
}
}
}
v___jp_6393_:
{
if (lean_obj_tag(v___y_6396_) == 1)
{
if (lean_obj_tag(v_a_6404_) == 0)
{
lean_object* v_val_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v_val_6405_ = lean_ctor_get(v___y_6396_, 0);
lean_inc(v_val_6405_);
lean_dec_ref_known(v___y_6396_, 1);
v___x_6406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6363_);
v___x_6407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6407_, 0, v_tk_6363_);
lean_ctor_set(v___x_6407_, 1, v___x_6406_);
v___y_6365_ = v___y_6395_;
v___y_6366_ = v___y_6394_;
v___y_6367_ = v_val_6405_;
v___y_6368_ = v___y_6397_;
v___y_6369_ = v___y_6398_;
v___y_6370_ = v___y_6401_;
v___y_6371_ = v___y_6400_;
v___y_6372_ = v___y_6399_;
v___y_6373_ = v___y_6402_;
v___y_6374_ = v___y_6403_;
v___y_6375_ = v___x_6407_;
goto v___jp_6364_;
}
else
{
lean_object* v_val_6408_; lean_object* v_val_6409_; 
v_val_6408_ = lean_ctor_get(v___y_6396_, 0);
lean_inc(v_val_6408_);
lean_dec_ref_known(v___y_6396_, 1);
v_val_6409_ = lean_ctor_get(v_a_6404_, 0);
lean_inc(v_val_6409_);
lean_dec_ref_known(v_a_6404_, 1);
v___y_6365_ = v___y_6395_;
v___y_6366_ = v___y_6394_;
v___y_6367_ = v_val_6408_;
v___y_6368_ = v___y_6397_;
v___y_6369_ = v___y_6398_;
v___y_6370_ = v___y_6401_;
v___y_6371_ = v___y_6400_;
v___y_6372_ = v___y_6399_;
v___y_6373_ = v___y_6402_;
v___y_6374_ = v___y_6403_;
v___y_6375_ = v_val_6409_;
goto v___jp_6364_;
}
}
else
{
lean_dec(v___y_6396_);
if (lean_obj_tag(v___y_6394_) == 1)
{
if (lean_obj_tag(v_a_6404_) == 0)
{
lean_object* v_val_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; 
v_val_6410_ = lean_ctor_get(v___y_6394_, 0);
lean_inc(v_val_6410_);
lean_dec_ref_known(v___y_6394_, 1);
v___x_6411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6412_, 0, v_tk_6363_);
lean_ctor_set(v___x_6412_, 1, v___x_6411_);
v___y_6337_ = v_val_6410_;
v___y_6338_ = v___y_6395_;
v___y_6339_ = v___y_6397_;
v___y_6340_ = v___y_6398_;
v___y_6341_ = v___y_6401_;
v___y_6342_ = v___y_6400_;
v___y_6343_ = v___y_6399_;
v___y_6344_ = v___y_6402_;
v___y_6345_ = v___y_6403_;
v___y_6346_ = v___x_6412_;
goto v___jp_6336_;
}
else
{
lean_object* v_val_6413_; lean_object* v_val_6414_; 
lean_dec(v_tk_6363_);
v_val_6413_ = lean_ctor_get(v___y_6394_, 0);
lean_inc(v_val_6413_);
lean_dec_ref_known(v___y_6394_, 1);
v_val_6414_ = lean_ctor_get(v_a_6404_, 0);
lean_inc(v_val_6414_);
lean_dec_ref_known(v_a_6404_, 1);
v___y_6337_ = v_val_6413_;
v___y_6338_ = v___y_6395_;
v___y_6339_ = v___y_6397_;
v___y_6340_ = v___y_6398_;
v___y_6341_ = v___y_6401_;
v___y_6342_ = v___y_6400_;
v___y_6343_ = v___y_6399_;
v___y_6344_ = v___y_6402_;
v___y_6345_ = v___y_6403_;
v___y_6346_ = v_val_6414_;
goto v___jp_6336_;
}
}
else
{
lean_object* v___x_6415_; lean_object* v___x_6416_; 
lean_dec(v_a_6404_);
lean_dec(v___y_6394_);
lean_dec(v_tk_6363_);
v___x_6415_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6416_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6415_, v___y_6397_, v___y_6403_, v___y_6398_, v___y_6399_);
return v___x_6416_;
}
}
}
v___jp_6417_:
{
if (lean_obj_tag(v___y_6419_) == 0)
{
lean_object* v___x_6429_; 
v___x_6429_ = lean_box(0);
v___y_6394_ = v___y_6418_;
v___y_6395_ = v___y_6423_;
v___y_6396_ = v_val_x3f_6420_;
v___y_6397_ = v___y_6425_;
v___y_6398_ = v___y_6427_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___y_6421_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6422_;
v___y_6403_ = v___y_6426_;
v_a_6404_ = v___x_6429_;
goto v___jp_6393_;
}
else
{
lean_object* v_val_6430_; lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6447_; 
v_val_6430_ = lean_ctor_get(v___y_6419_, 0);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___y_6419_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6432_ = v___y_6419_;
v_isShared_6433_ = v_isSharedCheck_6447_;
goto v_resetjp_6431_;
}
else
{
lean_inc(v_val_6430_);
lean_dec(v___y_6419_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6447_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
lean_object* v___x_6434_; 
v___x_6434_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6430_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
if (lean_obj_tag(v___x_6434_) == 0)
{
lean_object* v_a_6435_; lean_object* v___x_6437_; 
v_a_6435_ = lean_ctor_get(v___x_6434_, 0);
lean_inc(v_a_6435_);
lean_dec_ref_known(v___x_6434_, 1);
if (v_isShared_6433_ == 0)
{
lean_ctor_set(v___x_6432_, 0, v_a_6435_);
v___x_6437_ = v___x_6432_;
goto v_reusejp_6436_;
}
else
{
lean_object* v_reuseFailAlloc_6438_; 
v_reuseFailAlloc_6438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6438_, 0, v_a_6435_);
v___x_6437_ = v_reuseFailAlloc_6438_;
goto v_reusejp_6436_;
}
v_reusejp_6436_:
{
v___y_6394_ = v___y_6418_;
v___y_6395_ = v___y_6423_;
v___y_6396_ = v_val_x3f_6420_;
v___y_6397_ = v___y_6425_;
v___y_6398_ = v___y_6427_;
v___y_6399_ = v___y_6428_;
v___y_6400_ = v___y_6421_;
v___y_6401_ = v___y_6424_;
v___y_6402_ = v___y_6422_;
v___y_6403_ = v___y_6426_;
v_a_6404_ = v___x_6437_;
goto v___jp_6393_;
}
}
else
{
lean_object* v_a_6439_; lean_object* v___x_6441_; uint8_t v_isShared_6442_; uint8_t v_isSharedCheck_6446_; 
lean_del_object(v___x_6432_);
lean_dec(v_val_x3f_6420_);
lean_dec(v___y_6418_);
lean_dec(v_tk_6363_);
v_a_6439_ = lean_ctor_get(v___x_6434_, 0);
v_isSharedCheck_6446_ = !lean_is_exclusive(v___x_6434_);
if (v_isSharedCheck_6446_ == 0)
{
v___x_6441_ = v___x_6434_;
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
else
{
lean_inc(v_a_6439_);
lean_dec(v___x_6434_);
v___x_6441_ = lean_box(0);
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
v_resetjp_6440_:
{
lean_object* v___x_6444_; 
if (v_isShared_6442_ == 0)
{
v___x_6444_ = v___x_6441_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
v___x_6444_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
return v___x_6444_;
}
}
}
}
}
}
v___jp_6449_:
{
lean_object* v___x_6461_; lean_object* v___x_6462_; uint8_t v___x_6463_; 
v___x_6461_ = lean_unsigned_to_nat(3u);
v___x_6462_ = l_Lean_Syntax_getArg(v_stx_6326_, v___x_6461_);
lean_dec(v_stx_6326_);
v___x_6463_ = l_Lean_Syntax_isNone(v___x_6462_);
if (v___x_6463_ == 0)
{
uint8_t v___x_6464_; 
lean_inc(v___x_6462_);
v___x_6464_ = l_Lean_Syntax_matchesNull(v___x_6462_, v___y_6450_);
if (v___x_6464_ == 0)
{
lean_object* v___x_6465_; 
lean_dec(v___x_6462_);
lean_dec(v_ty_x3f_6452_);
lean_dec(v___y_6451_);
lean_dec(v_tk_6363_);
v___x_6465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6465_;
}
else
{
lean_object* v___x_6466_; lean_object* v_val_x3f_6467_; lean_object* v___x_6468_; 
v___x_6466_ = l_Lean_Syntax_getArg(v___x_6462_, v___x_6448_);
lean_dec(v___x_6462_);
v_val_x3f_6467_ = l_Lean_Syntax_getArgs(v___x_6466_);
lean_dec(v___x_6466_);
v___x_6468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6468_, 0, v_val_x3f_6467_);
v___y_6418_ = v_ty_x3f_6452_;
v___y_6419_ = v___y_6451_;
v_val_x3f_6420_ = v___x_6468_;
v___y_6421_ = v___y_6453_;
v___y_6422_ = v___y_6454_;
v___y_6423_ = v___y_6455_;
v___y_6424_ = v___y_6456_;
v___y_6425_ = v___y_6457_;
v___y_6426_ = v___y_6458_;
v___y_6427_ = v___y_6459_;
v___y_6428_ = v___y_6460_;
goto v___jp_6417_;
}
}
else
{
lean_object* v___x_6469_; 
lean_dec(v___x_6462_);
v___x_6469_ = lean_box(0);
v___y_6418_ = v_ty_x3f_6452_;
v___y_6419_ = v___y_6451_;
v_val_x3f_6420_ = v___x_6469_;
v___y_6421_ = v___y_6453_;
v___y_6422_ = v___y_6454_;
v___y_6423_ = v___y_6455_;
v___y_6424_ = v___y_6456_;
v___y_6425_ = v___y_6457_;
v___y_6426_ = v___y_6458_;
v___y_6427_ = v___y_6459_;
v___y_6428_ = v___y_6460_;
goto v___jp_6417_;
}
}
v___jp_6470_:
{
lean_object* v___x_6480_; lean_object* v___x_6481_; uint8_t v___x_6482_; 
v___x_6480_ = lean_unsigned_to_nat(2u);
v___x_6481_ = l_Lean_Syntax_getArg(v_stx_6326_, v___x_6480_);
v___x_6482_ = l_Lean_Syntax_isNone(v___x_6481_);
if (v___x_6482_ == 0)
{
uint8_t v___x_6483_; 
lean_inc(v___x_6481_);
v___x_6483_ = l_Lean_Syntax_matchesNull(v___x_6481_, v___x_6480_);
if (v___x_6483_ == 0)
{
lean_object* v___x_6484_; 
lean_dec(v___x_6481_);
lean_dec(v_pat_x3f_6471_);
lean_dec(v_tk_6363_);
lean_dec(v_stx_6326_);
v___x_6484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6484_;
}
else
{
lean_object* v_ty_x3f_6485_; lean_object* v___x_6486_; 
v_ty_x3f_6485_ = l_Lean_Syntax_getArg(v___x_6481_, v___x_6448_);
lean_dec(v___x_6481_);
v___x_6486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6486_, 0, v_ty_x3f_6485_);
v___y_6450_ = v___x_6480_;
v___y_6451_ = v_pat_x3f_6471_;
v_ty_x3f_6452_ = v___x_6486_;
v___y_6453_ = v___y_6472_;
v___y_6454_ = v___y_6473_;
v___y_6455_ = v___y_6474_;
v___y_6456_ = v___y_6475_;
v___y_6457_ = v___y_6476_;
v___y_6458_ = v___y_6477_;
v___y_6459_ = v___y_6478_;
v___y_6460_ = v___y_6479_;
goto v___jp_6449_;
}
}
else
{
lean_object* v___x_6487_; 
lean_dec(v___x_6481_);
v___x_6487_ = lean_box(0);
v___y_6450_ = v___x_6480_;
v___y_6451_ = v_pat_x3f_6471_;
v_ty_x3f_6452_ = v___x_6487_;
v___y_6453_ = v___y_6472_;
v___y_6454_ = v___y_6473_;
v___y_6455_ = v___y_6474_;
v___y_6456_ = v___y_6475_;
v___y_6457_ = v___y_6476_;
v___y_6458_ = v___y_6477_;
v___y_6459_ = v___y_6478_;
v___y_6460_ = v___y_6479_;
goto v___jp_6449_;
}
}
}
v___jp_6336_:
{
lean_object* v___x_6347_; 
v___x_6347_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6344_, v___y_6339_, v___y_6345_, v___y_6340_, v___y_6343_);
if (lean_obj_tag(v___x_6347_) == 0)
{
lean_object* v_a_6348_; lean_object* v___f_6349_; lean_object* v___x_6350_; 
v_a_6348_ = lean_ctor_get(v___x_6347_, 0);
lean_inc_n(v_a_6348_, 2);
lean_dec_ref_known(v___x_6347_, 1);
v___f_6349_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6349_, 0, v___y_6346_);
lean_closure_set(v___f_6349_, 1, v___y_6337_);
lean_closure_set(v___f_6349_, 2, v_a_6348_);
v___x_6350_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6348_, v___f_6349_, v___y_6342_, v___y_6344_, v___y_6338_, v___y_6341_, v___y_6339_, v___y_6345_, v___y_6340_, v___y_6343_);
return v___x_6350_;
}
else
{
lean_object* v_a_6351_; lean_object* v___x_6353_; uint8_t v_isShared_6354_; uint8_t v_isSharedCheck_6358_; 
lean_dec_ref(v___y_6346_);
lean_dec(v___y_6337_);
v_a_6351_ = lean_ctor_get(v___x_6347_, 0);
v_isSharedCheck_6358_ = !lean_is_exclusive(v___x_6347_);
if (v_isSharedCheck_6358_ == 0)
{
v___x_6353_ = v___x_6347_;
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
else
{
lean_inc(v_a_6351_);
lean_dec(v___x_6347_);
v___x_6353_ = lean_box(0);
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
v_resetjp_6352_:
{
lean_object* v___x_6356_; 
if (v_isShared_6354_ == 0)
{
v___x_6356_ = v___x_6353_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
v___x_6356_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
return v___x_6356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_, lean_object* v_a_6502_, lean_object* v_a_6503_, lean_object* v_a_6504_, lean_object* v_a_6505_, lean_object* v_a_6506_, lean_object* v_a_6507_){
_start:
{
lean_object* v_res_6508_; 
v_res_6508_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6498_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_, v_a_6503_, v_a_6504_, v_a_6505_, v_a_6506_);
lean_dec(v_a_6506_);
lean_dec_ref(v_a_6505_);
lean_dec(v_a_6504_);
lean_dec_ref(v_a_6503_);
lean_dec(v_a_6502_);
lean_dec_ref(v_a_6501_);
lean_dec(v_a_6500_);
lean_dec_ref(v_a_6499_);
return v_res_6508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6509_, lean_object* v_msg_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v___x_6520_; 
v___x_6520_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6510_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
return v___x_6520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6521_, lean_object* v_msg_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_){
_start:
{
lean_object* v_res_6532_; 
v_res_6532_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6521_, v_msg_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_);
lean_dec(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
lean_dec(v___y_6524_);
lean_dec_ref(v___y_6523_);
return v_res_6532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; 
v___x_6538_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6539_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6541_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6542_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6538_, v___x_6539_, v___x_6540_, v___x_6541_);
return v___x_6542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6543_){
_start:
{
lean_object* v_res_6544_; 
v_res_6544_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6545_, lean_object* v_ty_x3f_6546_, lean_object* v_a_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_){
_start:
{
lean_object* v___x_6557_; 
v___x_6557_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6545_, v_ty_x3f_6546_, v_a_6547_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6559_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
lean_inc(v_a_6558_);
lean_dec_ref_known(v___x_6557_, 1);
v___x_6559_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6558_, v___y_6549_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
return v___x_6559_;
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
v_a_6560_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6557_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6557_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
return v___x_6565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6568_, lean_object* v_ty_x3f_6569_, lean_object* v_a_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_){
_start:
{
lean_object* v_res_6580_; 
v_res_6580_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6568_, v_ty_x3f_6569_, v_a_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_);
lean_dec(v___y_6578_);
lean_dec_ref(v___y_6577_);
lean_dec(v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec(v___y_6574_);
lean_dec_ref(v___y_6573_);
lean_dec(v___y_6572_);
lean_dec_ref(v___y_6571_);
return v_res_6580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_){
_start:
{
lean_object* v___x_6597_; uint8_t v___x_6598_; 
v___x_6597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6587_);
v___x_6598_ = l_Lean_Syntax_isOfKind(v_stx_6587_, v___x_6597_);
if (v___x_6598_ == 0)
{
lean_object* v___x_6599_; 
lean_dec(v_stx_6587_);
v___x_6599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6599_;
}
else
{
lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v_ty_x3f_6603_; lean_object* v___y_6604_; lean_object* v___y_6605_; lean_object* v___y_6606_; lean_object* v___y_6607_; lean_object* v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; lean_object* v___x_6625_; lean_object* v___x_6626_; uint8_t v___x_6627_; 
v___x_6600_ = lean_unsigned_to_nat(1u);
v___x_6601_ = l_Lean_Syntax_getArg(v_stx_6587_, v___x_6600_);
v___x_6625_ = lean_unsigned_to_nat(2u);
v___x_6626_ = l_Lean_Syntax_getArg(v_stx_6587_, v___x_6625_);
lean_dec(v_stx_6587_);
v___x_6627_ = l_Lean_Syntax_isNone(v___x_6626_);
if (v___x_6627_ == 0)
{
uint8_t v___x_6628_; 
lean_inc(v___x_6626_);
v___x_6628_ = l_Lean_Syntax_matchesNull(v___x_6626_, v___x_6625_);
if (v___x_6628_ == 0)
{
lean_object* v___x_6629_; 
lean_dec(v___x_6626_);
lean_dec(v___x_6601_);
v___x_6629_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6629_;
}
else
{
lean_object* v_ty_x3f_6630_; lean_object* v___x_6631_; 
v_ty_x3f_6630_ = l_Lean_Syntax_getArg(v___x_6626_, v___x_6600_);
lean_dec(v___x_6626_);
v___x_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6631_, 0, v_ty_x3f_6630_);
v_ty_x3f_6603_ = v___x_6631_;
v___y_6604_ = v_a_6588_;
v___y_6605_ = v_a_6589_;
v___y_6606_ = v_a_6590_;
v___y_6607_ = v_a_6591_;
v___y_6608_ = v_a_6592_;
v___y_6609_ = v_a_6593_;
v___y_6610_ = v_a_6594_;
v___y_6611_ = v_a_6595_;
goto v___jp_6602_;
}
}
else
{
lean_object* v___x_6632_; 
lean_dec(v___x_6626_);
v___x_6632_ = lean_box(0);
v_ty_x3f_6603_ = v___x_6632_;
v___y_6604_ = v_a_6588_;
v___y_6605_ = v_a_6589_;
v___y_6606_ = v_a_6590_;
v___y_6607_ = v_a_6591_;
v___y_6608_ = v_a_6592_;
v___y_6609_ = v_a_6593_;
v___y_6610_ = v_a_6594_;
v___y_6611_ = v_a_6595_;
goto v___jp_6602_;
}
v___jp_6602_:
{
lean_object* v___x_6612_; 
v___x_6612_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6605_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_);
if (lean_obj_tag(v___x_6612_) == 0)
{
lean_object* v_a_6613_; lean_object* v_pats_6614_; lean_object* v___f_6615_; lean_object* v___x_6616_; 
v_a_6613_ = lean_ctor_get(v___x_6612_, 0);
lean_inc_n(v_a_6613_, 2);
lean_dec_ref_known(v___x_6612_, 1);
v_pats_6614_ = l_Lean_Syntax_getArgs(v___x_6601_);
lean_dec(v___x_6601_);
v___f_6615_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6615_, 0, v_pats_6614_);
lean_closure_set(v___f_6615_, 1, v_ty_x3f_6603_);
lean_closure_set(v___f_6615_, 2, v_a_6613_);
v___x_6616_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6613_, v___f_6615_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_);
return v___x_6616_;
}
else
{
lean_object* v_a_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6624_; 
lean_dec(v_ty_x3f_6603_);
lean_dec(v___x_6601_);
v_a_6617_ = lean_ctor_get(v___x_6612_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6612_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6619_ = v___x_6612_;
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_a_6617_);
lean_dec(v___x_6612_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v___x_6622_; 
if (v_isShared_6620_ == 0)
{
v___x_6622_ = v___x_6619_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_a_6617_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
return v___x_6622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6633_, lean_object* v_a_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_){
_start:
{
lean_object* v_res_6643_; 
v_res_6643_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6633_, v_a_6634_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_, v_a_6641_);
lean_dec(v_a_6641_);
lean_dec_ref(v_a_6640_);
lean_dec(v_a_6639_);
lean_dec_ref(v_a_6638_);
lean_dec(v_a_6637_);
lean_dec_ref(v_a_6636_);
lean_dec(v_a_6635_);
lean_dec_ref(v_a_6634_);
return v_res_6643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; 
v___x_6649_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6652_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6653_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6649_, v___x_6650_, v___x_6651_, v___x_6652_);
return v___x_6653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6654_){
_start:
{
lean_object* v_res_6655_; 
v_res_6655_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6655_;
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
