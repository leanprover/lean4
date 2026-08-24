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
lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1387_; uint8_t v_fst_1388_; lean_object* v_snd_1389_; lean_object* v_snd_1390_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1417_; 
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
v___x_1352_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_1351_, v_paramInfo_1343_, v___y_1350_, v_params_1321_, v___y_1349_);
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
v___x_1361_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v_ref_1320_, v_params_1321_, v___x_1360_, v_tail_1334_, v___y_1348_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
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
v___y_1348_ = v_snd_1390_;
v___y_1349_ = v_snd_1389_;
v___y_1350_ = v_fst_1388_;
v___y_1351_ = v_ref_1391_;
goto v___jp_1347_;
}
v___jp_1392_:
{
lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; uint8_t v___x_1398_; 
lean_inc_ref(v___y_1393_);
v___x_1395_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_1393_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_fst_1396_);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_unbox(v_fst_1396_);
lean_dec(v_fst_1396_);
v___y_1387_ = v___y_1393_;
v_fst_1388_ = v___x_1398_;
v_snd_1389_ = v_snd_1397_;
v_snd_1390_ = v___y_1394_;
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
v___y_1393_ = v___y_1400_;
v___y_1394_ = v___y_1402_;
goto v___jp_1392_;
}
}
else
{
lean_dec(v___y_1401_);
lean_del_object(v___x_1345_);
lean_dec(v_x_1324_);
v___y_1393_ = v___y_1400_;
v___y_1394_ = v___y_1402_;
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
lean_object* v_ks_1760_; lean_object* v_vs_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1779_; 
v_ks_1760_ = lean_ctor_get(v_x_1709_, 0);
v_vs_1761_ = lean_ctor_get(v_x_1709_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1763_ = v_x_1709_;
v_isShared_1764_ = v_isSharedCheck_1779_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_vs_1761_);
lean_inc(v_ks_1760_);
lean_dec(v_x_1709_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1779_;
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
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_ks_1760_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_vs_1761_);
v___x_1766_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_newNode_1767_; size_t v___x_1768_; uint8_t v___x_1769_; 
v_newNode_1767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v___x_1766_, v_x_1712_, v_x_1713_);
v___x_1768_ = ((size_t)7ULL);
v___x_1769_ = lean_usize_dec_le(v___x_1768_, v_x_1711_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1767_);
v___x_1771_ = lean_unsigned_to_nat(4u);
v___x_1772_ = lean_nat_dec_lt(v___x_1770_, v___x_1771_);
lean_dec(v___x_1770_);
if (v___x_1772_ == 0)
{
lean_object* v_ks_1773_; lean_object* v_vs_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_ks_1773_ = lean_ctor_get(v_newNode_1767_, 0);
lean_inc_ref(v_ks_1773_);
v_vs_1774_ = lean_ctor_get(v_newNode_1767_, 1);
lean_inc_ref(v_vs_1774_);
lean_dec_ref(v_newNode_1767_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___closed__0);
v___x_1777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_x_1711_, v_ks_1773_, v_vs_1774_, v___x_1775_, v___x_1776_);
lean_dec_ref(v_vs_1774_);
lean_dec_ref(v_ks_1773_);
return v___x_1777_;
}
else
{
return v_newNode_1767_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(size_t v_depth_1780_, lean_object* v_keys_1781_, lean_object* v_vals_1782_, lean_object* v_i_1783_, lean_object* v_entries_1784_){
_start:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_array_get_size(v_keys_1781_);
v___x_1786_ = lean_nat_dec_lt(v_i_1783_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v_i_1783_);
return v_entries_1784_;
}
else
{
lean_object* v_k_1787_; lean_object* v_v_1788_; uint64_t v___x_1789_; size_t v_h_1790_; size_t v___x_1791_; lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v_h_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_k_1787_ = lean_array_fget_borrowed(v_keys_1781_, v_i_1783_);
v_v_1788_ = lean_array_fget_borrowed(v_vals_1782_, v_i_1783_);
v___x_1789_ = l_Lean_instHashableMVarId_hash(v_k_1787_);
v_h_1790_ = lean_uint64_to_usize(v___x_1789_);
v___x_1791_ = ((size_t)5ULL);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_sub(v_depth_1780_, v___x_1793_);
v___x_1795_ = lean_usize_mul(v___x_1791_, v___x_1794_);
v_h_1796_ = lean_usize_shift_right(v_h_1790_, v___x_1795_);
v___x_1797_ = lean_nat_add(v_i_1783_, v___x_1792_);
lean_dec(v_i_1783_);
lean_inc(v_v_1788_);
lean_inc(v_k_1787_);
v___x_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_entries_1784_, v_h_1796_, v_depth_1780_, v_k_1787_, v_v_1788_);
v_i_1783_ = v___x_1797_;
v_entries_1784_ = v___x_1798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_depth_1800_, lean_object* v_keys_1801_, lean_object* v_vals_1802_, lean_object* v_i_1803_, lean_object* v_entries_1804_){
_start:
{
size_t v_depth_boxed_1805_; lean_object* v_res_1806_; 
v_depth_boxed_1805_ = lean_unbox_usize(v_depth_1800_);
lean_dec(v_depth_1800_);
v_res_1806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_boxed_1805_, v_keys_1801_, v_vals_1802_, v_i_1803_, v_entries_1804_);
lean_dec_ref(v_vals_1802_);
lean_dec_ref(v_keys_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg___boxed(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
size_t v_x_18704__boxed_1812_; size_t v_x_18705__boxed_1813_; lean_object* v_res_1814_; 
v_x_18704__boxed_1812_ = lean_unbox_usize(v_x_1808_);
lean_dec(v_x_1808_);
v_x_18705__boxed_1813_ = lean_unbox_usize(v_x_1809_);
lean_dec(v_x_1809_);
v_res_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1807_, v_x_18704__boxed_1812_, v_x_18705__boxed_1813_, v_x_1810_, v_x_1811_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
uint64_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = l_Lean_instHashableMVarId_hash(v_x_1816_);
v___x_1819_ = lean_uint64_to_usize(v___x_1818_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_1815_, v___x_1819_, v___x_1820_, v_x_1816_, v_x_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(lean_object* v_mvarId_1822_, lean_object* v_val_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_mctx_1827_; lean_object* v_cache_1828_; lean_object* v_zetaDeltaFVarIds_1829_; lean_object* v_postponed_1830_; lean_object* v_diag_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1860_; 
v___x_1826_ = lean_st_ref_take(v___y_1824_);
v_mctx_1827_ = lean_ctor_get(v___x_1826_, 0);
v_cache_1828_ = lean_ctor_get(v___x_1826_, 1);
v_zetaDeltaFVarIds_1829_ = lean_ctor_get(v___x_1826_, 2);
v_postponed_1830_ = lean_ctor_get(v___x_1826_, 3);
v_diag_1831_ = lean_ctor_get(v___x_1826_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1833_ = v___x_1826_;
v_isShared_1834_ = v_isSharedCheck_1860_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_diag_1831_);
lean_inc(v_postponed_1830_);
lean_inc(v_zetaDeltaFVarIds_1829_);
lean_inc(v_cache_1828_);
lean_inc(v_mctx_1827_);
lean_dec(v___x_1826_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1860_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_depth_1835_; lean_object* v_levelAssignDepth_1836_; lean_object* v_lmvarCounter_1837_; lean_object* v_mvarCounter_1838_; lean_object* v_lDecls_1839_; lean_object* v_decls_1840_; lean_object* v_userNames_1841_; lean_object* v_lAssignment_1842_; lean_object* v_eAssignment_1843_; lean_object* v_dAssignment_1844_; lean_object* v_instanceTypedMVars_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
v_depth_1835_ = lean_ctor_get(v_mctx_1827_, 0);
v_levelAssignDepth_1836_ = lean_ctor_get(v_mctx_1827_, 1);
v_lmvarCounter_1837_ = lean_ctor_get(v_mctx_1827_, 2);
v_mvarCounter_1838_ = lean_ctor_get(v_mctx_1827_, 3);
v_lDecls_1839_ = lean_ctor_get(v_mctx_1827_, 4);
v_decls_1840_ = lean_ctor_get(v_mctx_1827_, 5);
v_userNames_1841_ = lean_ctor_get(v_mctx_1827_, 6);
v_lAssignment_1842_ = lean_ctor_get(v_mctx_1827_, 7);
v_eAssignment_1843_ = lean_ctor_get(v_mctx_1827_, 8);
v_dAssignment_1844_ = lean_ctor_get(v_mctx_1827_, 9);
v_instanceTypedMVars_1845_ = lean_ctor_get(v_mctx_1827_, 10);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_mctx_1827_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1847_ = v_mctx_1827_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_instanceTypedMVars_1845_);
lean_inc(v_dAssignment_1844_);
lean_inc(v_eAssignment_1843_);
lean_inc(v_lAssignment_1842_);
lean_inc(v_userNames_1841_);
lean_inc(v_decls_1840_);
lean_inc(v_lDecls_1839_);
lean_inc(v_mvarCounter_1838_);
lean_inc(v_lmvarCounter_1837_);
lean_inc(v_levelAssignDepth_1836_);
lean_inc(v_depth_1835_);
lean_dec(v_mctx_1827_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_eAssignment_1843_, v_mvarId_1822_, v_val_1823_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 8, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_depth_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_levelAssignDepth_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_lmvarCounter_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_mvarCounter_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_lDecls_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_decls_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_userNames_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_lAssignment_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v_dAssignment_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_instanceTypedMVars_1845_);
v___x_1851_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1851_);
v___x_1853_ = v___x_1833_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_cache_1828_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_zetaDeltaFVarIds_1829_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_postponed_1830_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_diag_1831_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_st_ref_put(v___y_1824_, v___x_1853_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg___boxed(lean_object* v_mvarId_1861_, lean_object* v_val_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_1861_, v_val_1862_, v___y_1863_);
lean_dec(v___y_1863_);
return v_res_1865_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_15186__overap_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___closed__0);
v___x_15186__overap_1876_ = lean_panic_fn_borrowed(v___x_1875_, v_msg_1867_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1869_);
lean_inc_ref(v___y_1868_);
v___x_1877_ = lean_apply_7(v___x_15186__overap_1876_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, lean_box(0));
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4___boxed(lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v_msg_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(lean_object* v_as_1887_, size_t v_i_1888_, size_t v_stop_1889_, lean_object* v_b_1890_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_usize_dec_eq(v_i_1888_, v_stop_1889_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; 
v___x_1892_ = lean_array_uget_borrowed(v_as_1887_, v_i_1888_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
lean_inc(v_snd_1894_);
v___x_1895_ = l_Lean_mkFVar(v_snd_1894_);
lean_inc(v_fst_1893_);
v___x_1896_ = l_Lean_Meta_FVarSubst_insert(v_b_1890_, v_fst_1893_, v___x_1895_);
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = lean_usize_add(v_i_1888_, v___x_1897_);
v_i_1888_ = v___x_1898_;
v_b_1890_ = v___x_1896_;
goto _start;
}
else
{
return v_b_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6___boxed(lean_object* v_as_1900_, lean_object* v_i_1901_, lean_object* v_stop_1902_, lean_object* v_b_1903_){
_start:
{
size_t v_i_boxed_1904_; size_t v_stop_boxed_1905_; lean_object* v_res_1906_; 
v_i_boxed_1904_ = lean_unbox_usize(v_i_1901_);
lean_dec(v_i_1901_);
v_stop_boxed_1905_ = lean_unbox_usize(v_stop_1902_);
lean_dec(v_stop_1902_);
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v_as_1900_, v_i_boxed_1904_, v_stop_boxed_1905_, v_b_1903_);
lean_dec_ref(v_as_1900_);
return v_res_1906_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_1907_; lean_object* v_dummy_1908_; 
v___x_1907_ = lean_box(0);
v_dummy_1908_ = l_Lean_Expr_sort___override(v___x_1907_);
return v_dummy_1908_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_1913_ = lean_unsigned_to_nat(62u);
v___x_1914_ = lean_unsigned_to_nat(323u);
v___x_1915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_1916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_1917_ = l_mkPanicMessageWithDecl(v___x_1916_, v___x_1915_, v___x_1914_, v___x_1913_, v___x_1912_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(lean_object* v___x_1918_, lean_object* v___x_1919_, lean_object* v_snd_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v___x_1923_, lean_object* v_e_1924_, lean_object* v___x_1925_, lean_object* v_head_1926_, lean_object* v_fst_1927_, lean_object* v_tail_1928_, uint8_t v___x_1929_, lean_object* v_snd_1930_, lean_object* v___x_1931_, lean_object* v_fs_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Meta_getElimInfo(v___x_1918_, v___x_1919_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
lean_inc(v_snd_1920_);
v___x_1942_ = l_Lean_MVarId_getTag(v_snd_1920_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
lean_inc(v_a_1941_);
v___x_1944_ = l_Lean_Elab_Tactic_ElimApp_mkElimApp(v_a_1941_, v___x_1921_, v_a_1943_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v_elimApp_1946_; lean_object* v_alts_1947_; lean_object* v_motivePos_1948_; lean_object* v_nargs_1949_; lean_object* v_dummy_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_elimApp_1946_ = lean_ctor_get(v_a_1945_, 0);
lean_inc_ref_n(v_elimApp_1946_, 2);
v_alts_1947_ = lean_ctor_get(v_a_1945_, 3);
lean_inc_ref(v_alts_1947_);
lean_dec(v_a_1945_);
v_motivePos_1948_ = lean_ctor_get(v_a_1941_, 2);
lean_inc(v_motivePos_1948_);
lean_dec(v_a_1941_);
v_nargs_1949_ = l_Lean_Expr_getAppNumArgs(v_elimApp_1946_);
v_dummy_1950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__0);
lean_inc(v_nargs_1949_);
v___x_1951_ = lean_mk_array(v_nargs_1949_, v_dummy_1950_);
v___x_1952_ = lean_nat_sub(v_nargs_1949_, v___x_1922_);
lean_dec(v_nargs_1949_);
v___x_1953_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_elimApp_1946_, v___x_1951_, v___x_1952_);
v___x_1954_ = lean_array_get(v___x_1923_, v___x_1953_, v_motivePos_1948_);
lean_dec(v_motivePos_1948_);
lean_dec_ref(v___x_1953_);
v___x_1955_ = l_Lean_Expr_mvarId_x21(v___x_1954_);
lean_dec(v___x_1954_);
v___x_1956_ = l_Lean_Expr_fvarId_x21(v_e_1924_);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___x_1922_);
lean_inc_ref(v___x_1957_);
v___x_1958_ = lean_array_push(v___x_1957_, v___x_1956_);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1925_);
lean_inc(v_snd_1920_);
v___x_1960_ = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(v_snd_1920_, v___x_1955_, v___x_1958_, v___x_1959_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1961_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_snd_1920_, v_elimApp_1946_, v___y_1936_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = lean_array_get_size(v_alts_1947_);
v___x_1963_ = lean_nat_dec_eq(v___x_1962_, v___x_1922_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_alts_1947_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
v___x_1964_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__4);
v___x_1965_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_1964_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1965_;
}
else
{
lean_object* v___x_1966_; lean_object* v_name_1967_; lean_object* v_mvarId_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2040_; 
v___x_1966_ = lean_array_fget(v_alts_1947_, v___x_1925_);
lean_dec_ref(v_alts_1947_);
v_name_1967_ = lean_ctor_get(v___x_1966_, 0);
v_mvarId_1968_ = lean_ctor_get(v___x_1966_, 2);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_1966_, 1);
lean_dec(v_unused_2041_);
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_2040_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_mvarId_1968_);
lean_inc(v_name_1967_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2040_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_MVarId_intro(v_mvarId_1968_, v_head_1926_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2031_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v_fst_1974_ = lean_ctor_get(v_a_1973_, 0);
v_snd_1975_ = lean_ctor_get(v_a_1973_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1977_ = v_a_1973_;
v_isShared_1978_ = v_isSharedCheck_2031_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snd_1975_);
lean_inc(v_fst_1974_);
lean_dec(v_a_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2031_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_array_get_size(v_fst_1927_);
v___x_1980_ = l_Lean_Meta_introNCore(v_snd_1975_, v___x_1979_, v_tail_1928_, v___x_1929_, v___x_1963_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2022_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2022_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2022_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2021_; 
v_fst_1985_ = lean_ctor_get(v_a_1981_, 0);
v_snd_1986_ = lean_ctor_get(v_a_1981_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1988_ = v_a_1981_;
v_isShared_1989_ = v_isSharedCheck_2021_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_snd_1986_);
lean_inc(v_fst_1985_);
lean_dec(v_a_1981_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2021_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___y_1991_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2011_ = l_Array_zip___redArg(v_fst_1927_, v_fst_1985_);
lean_dec(v_fst_1985_);
v___x_2012_ = lean_array_get_size(v___x_2011_);
v___x_2013_ = lean_nat_dec_lt(v___x_1925_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v___x_2011_);
v___y_1991_ = v_fs_1932_;
goto v___jp_1990_;
}
else
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_nat_dec_le(v___x_2012_, v___x_2012_);
if (v___x_2014_ == 0)
{
if (v___x_2013_ == 0)
{
lean_dec_ref(v___x_2011_);
v___y_1991_ = v_fs_1932_;
goto v___jp_1990_;
}
else
{
size_t v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = lean_usize_of_nat(v___x_2012_);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2011_, v___x_2015_, v___x_2016_, v_fs_1932_);
lean_dec_ref(v___x_2011_);
v___y_1991_ = v___x_2017_;
goto v___jp_1990_;
}
}
else
{
size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = lean_usize_of_nat(v___x_2012_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__6(v___x_2011_, v___x_2018_, v___x_2019_, v_fs_1932_);
lean_dec_ref(v___x_2011_);
v___y_1991_ = v___x_2020_;
goto v___jp_1990_;
}
}
v___jp_1990_:
{
lean_object* v___x_1993_; 
lean_inc(v_name_1967_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_snd_1930_);
lean_ctor_set(v___x_1988_, 0, v_name_1967_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_name_1967_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_snd_1930_);
v___x_1993_ = v_reuseFailAlloc_2010_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_mkFVar(v_fst_1974_);
v___x_1997_ = lean_array_push(v___x_1931_, v___x_1996_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 2, v___y_1991_);
lean_ctor_set(v___x_1970_, 1, v___x_1997_);
lean_ctor_set(v___x_1970_, 0, v_snd_1986_);
v___x_1999_ = v___x_1970_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_snd_1986_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v___y_1991_);
v___x_1999_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_name_1967_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_array_push(v___x_1957_, v___x_2001_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_2002_);
lean_ctor_set(v___x_1977_, 0, v___x_1995_);
v___x_2004_ = v___x_1977_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2004_);
v___x_2006_ = v___x_1983_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
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
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_del_object(v___x_1977_);
lean_dec(v_fst_1974_);
lean_del_object(v___x_1970_);
lean_dec(v_name_1967_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
v_a_2023_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1980_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1980_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_del_object(v___x_1970_);
lean_dec(v_name_1967_);
lean_dec_ref(v___x_1957_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
v_a_2032_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1972_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1972_);
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
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_alts_1947_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
v_a_2042_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_1961_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_1961_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_alts_1947_);
lean_dec_ref(v_elimApp_1946_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
lean_dec(v_snd_1920_);
v_a_2050_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1960_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1960_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_1941_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
lean_dec(v_snd_1920_);
v_a_2058_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1944_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1944_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_1941_);
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
v_a_2066_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1942_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1942_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_fs_1932_);
lean_dec_ref(v___x_1931_);
lean_dec(v_snd_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_head_1926_);
lean_dec_ref(v___x_1921_);
lean_dec(v_snd_1920_);
v_a_2074_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1940_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1940_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2082_ = _args[0];
lean_object* v___x_2083_ = _args[1];
lean_object* v_snd_2084_ = _args[2];
lean_object* v___x_2085_ = _args[3];
lean_object* v___x_2086_ = _args[4];
lean_object* v___x_2087_ = _args[5];
lean_object* v_e_2088_ = _args[6];
lean_object* v___x_2089_ = _args[7];
lean_object* v_head_2090_ = _args[8];
lean_object* v_fst_2091_ = _args[9];
lean_object* v_tail_2092_ = _args[10];
lean_object* v___x_2093_ = _args[11];
lean_object* v_snd_2094_ = _args[12];
lean_object* v___x_2095_ = _args[13];
lean_object* v_fs_2096_ = _args[14];
lean_object* v___y_2097_ = _args[15];
lean_object* v___y_2098_ = _args[16];
lean_object* v___y_2099_ = _args[17];
lean_object* v___y_2100_ = _args[18];
lean_object* v___y_2101_ = _args[19];
lean_object* v___y_2102_ = _args[20];
lean_object* v___y_2103_ = _args[21];
_start:
{
uint8_t v___x_18989__boxed_2104_; lean_object* v_res_2105_; 
v___x_18989__boxed_2104_ = lean_unbox(v___x_2093_);
v_res_2105_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4(v___x_2082_, v___x_2083_, v_snd_2084_, v___x_2085_, v___x_2086_, v___x_2087_, v_e_2088_, v___x_2089_, v_head_2090_, v_fst_2091_, v_tail_2092_, v___x_18989__boxed_2104_, v_snd_2094_, v___x_2095_, v_fs_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec_ref(v_fst_2091_);
lean_dec(v___x_2089_);
lean_dec_ref(v_e_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v___x_2086_);
return v_res_2105_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__3));
v___x_2107_ = lean_unsigned_to_nat(76u);
v___x_2108_ = lean_unsigned_to_nat(315u);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__2));
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___closed__1));
v___x_2111_ = l_mkPanicMessageWithDecl(v___x_2110_, v___x_2109_, v___x_2108_, v___x_2107_, v___x_2106_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(uint8_t v___x_2119_, lean_object* v_e_2120_, lean_object* v___x_2121_, lean_object* v_g_2122_, lean_object* v___x_2123_, lean_object* v_fs_2124_, lean_object* v_pat_2125_, lean_object* v_____r_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2182_; lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2125_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__2));
v___y_2182_ = v___x_2189_;
goto v___jp_2181_;
}
else
{
lean_object* v_head_2190_; 
v_head_2190_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_head_2190_);
lean_dec_ref_known(v___x_2188_, 2);
v___y_2182_ = v_head_2190_;
goto v___jp_2181_;
}
v___jp_2134_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__0);
v___x_2136_ = l_panic___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__4(v___x_2135_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2136_;
}
v___jp_2137_:
{
uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v_fst_2149_; 
v___x_2141_ = 0;
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1));
v___x_2144_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1, v___x_2141_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 1, v___x_2119_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 2, v___x_2119_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 3, v___x_2119_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 4, v___x_2119_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 5, v___x_2119_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*1 + 6, v___x_2119_);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_mk_empty_array_with_capacity(v___x_2145_);
lean_inc_ref(v___x_2146_);
v___x_2147_ = lean_array_push(v___x_2146_, v___x_2144_);
v___x_2148_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_2140_, v___x_2147_, v___y_2138_, v___x_2142_, v___y_2139_);
lean_dec_ref(v___x_2147_);
v_fst_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_fst_2149_);
if (lean_obj_tag(v_fst_2149_) == 1)
{
lean_object* v_tail_2150_; 
v_tail_2150_ = lean_ctor_get(v_fst_2149_, 1);
lean_inc(v_tail_2150_);
if (lean_obj_tag(v_tail_2150_) == 0)
{
lean_object* v_snd_2151_; lean_object* v_head_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_snd_2151_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_snd_2151_);
lean_dec_ref(v___x_2148_);
v_head_2152_ = lean_ctor_get(v_fst_2149_, 0);
lean_inc(v_head_2152_);
lean_dec_ref_known(v_fst_2149_, 2);
lean_inc_ref(v_e_2120_);
lean_inc_ref(v___x_2146_);
v___x_2153_ = lean_array_push(v___x_2146_, v_e_2120_);
v___x_2154_ = l_Lean_Meta_getFVarsToGeneralize(v___x_2153_, v___x_2121_, v___x_2119_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = l_Lean_MVarId_revert(v_g_2122_, v_a_2155_, v___x_2119_, v___x_2119_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v_fst_2158_ = lean_ctor_get(v_a_2157_, 0);
lean_inc(v_fst_2158_);
v_snd_2159_ = lean_ctor_get(v_a_2157_, 1);
lean_inc_n(v_snd_2159_, 2);
lean_dec(v_a_2157_);
v___x_2160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__4));
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_box(v___x_2119_);
v___f_2163_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__4___boxed), 22, 15);
lean_closure_set(v___f_2163_, 0, v___x_2160_);
lean_closure_set(v___f_2163_, 1, v___x_2161_);
lean_closure_set(v___f_2163_, 2, v_snd_2159_);
lean_closure_set(v___f_2163_, 3, v___x_2153_);
lean_closure_set(v___f_2163_, 4, v___x_2145_);
lean_closure_set(v___f_2163_, 5, v___x_2123_);
lean_closure_set(v___f_2163_, 6, v_e_2120_);
lean_closure_set(v___f_2163_, 7, v___x_2142_);
lean_closure_set(v___f_2163_, 8, v_head_2152_);
lean_closure_set(v___f_2163_, 9, v_fst_2158_);
lean_closure_set(v___f_2163_, 10, v_tail_2150_);
lean_closure_set(v___f_2163_, 11, v___x_2162_);
lean_closure_set(v___f_2163_, 12, v_snd_2151_);
lean_closure_set(v___f_2163_, 13, v___x_2146_);
lean_closure_set(v___f_2163_, 14, v_fs_2124_);
v___x_2164_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_snd_2159_, v___f_2163_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2164_;
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___x_2153_);
lean_dec(v_head_2152_);
lean_dec(v_snd_2151_);
lean_dec_ref(v___x_2146_);
lean_dec(v_fs_2124_);
lean_dec_ref(v___x_2123_);
lean_dec_ref(v_e_2120_);
v_a_2165_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2156_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2156_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v___x_2153_);
lean_dec(v_head_2152_);
lean_dec(v_snd_2151_);
lean_dec_ref(v___x_2146_);
lean_dec(v_fs_2124_);
lean_dec_ref(v___x_2123_);
lean_dec(v_g_2122_);
lean_dec_ref(v_e_2120_);
v_a_2173_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2154_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2154_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_dec_ref_known(v_fst_2149_, 2);
lean_dec(v_tail_2150_);
lean_dec_ref(v___x_2148_);
lean_dec_ref(v___x_2146_);
lean_dec(v_fs_2124_);
lean_dec_ref(v___x_2123_);
lean_dec(v_g_2122_);
lean_dec(v___x_2121_);
lean_dec_ref(v_e_2120_);
goto v___jp_2134_;
}
}
else
{
lean_dec(v_fst_2149_);
lean_dec_ref(v___x_2148_);
lean_dec_ref(v___x_2146_);
lean_dec(v_fs_2124_);
lean_dec_ref(v___x_2123_);
lean_dec(v_g_2122_);
lean_dec(v___x_2121_);
lean_dec_ref(v_e_2120_);
goto v___jp_2134_;
}
}
v___jp_2181_:
{
lean_object* v___x_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v_ref_2186_; uint8_t v___x_2187_; 
lean_inc_ref(v___y_2182_);
v___x_2183_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v___y_2182_);
v_fst_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v___x_2183_);
v_ref_2186_ = lean_ctor_get(v___y_2182_, 0);
lean_inc(v_ref_2186_);
lean_dec_ref(v___y_2182_);
v___x_2187_ = lean_unbox(v_fst_2184_);
lean_dec(v_fst_2184_);
v___y_2138_ = v___x_2187_;
v___y_2139_ = v_snd_2185_;
v___y_2140_ = v_ref_2186_;
goto v___jp_2137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___boxed(lean_object* v___x_2191_, lean_object* v_e_2192_, lean_object* v___x_2193_, lean_object* v_g_2194_, lean_object* v___x_2195_, lean_object* v_fs_2196_, lean_object* v_pat_2197_, lean_object* v_____r_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_19361__boxed_2206_; lean_object* v_res_2207_; 
v___x_19361__boxed_2206_ = lean_unbox(v___x_2191_);
v_res_2207_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_19361__boxed_2206_, v_e_2192_, v___x_2193_, v_g_2194_, v___x_2195_, v_fs_2196_, v_pat_2197_, v_____r_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2207_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
if (lean_obj_tag(v_x_2208_) == 0)
{
if (lean_obj_tag(v_x_2209_) == 0)
{
uint8_t v___x_2210_; 
v___x_2210_ = 1;
return v___x_2210_;
}
else
{
uint8_t v___x_2211_; 
v___x_2211_ = 0;
return v___x_2211_;
}
}
else
{
if (lean_obj_tag(v_x_2209_) == 0)
{
uint8_t v___x_2212_; 
v___x_2212_ = 0;
return v___x_2212_;
}
else
{
lean_object* v_val_2213_; lean_object* v_val_2214_; uint8_t v___x_2215_; 
v_val_2213_ = lean_ctor_get(v_x_2208_, 0);
v_val_2214_ = lean_ctor_get(v_x_2209_, 0);
v___x_2215_ = lean_name_eq(v_val_2213_, v_val_2214_);
return v___x_2215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0___boxed(lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v_x_2216_, v_x_2217_);
lean_dec(v_x_2217_);
lean_dec(v_x_2216_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__1));
v___x_2224_ = l_Lean_MessageData_ofFormat(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
if (lean_obj_tag(v_x_2226_) == 0)
{
return v_x_2225_;
}
else
{
lean_object* v_head_2227_; lean_object* v_tail_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2250_; 
v_head_2227_ = lean_ctor_get(v_x_2226_, 0);
v_tail_2228_ = lean_ctor_get(v_x_2226_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_x_2226_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2230_ = v_x_2226_;
v_isShared_2231_ = v_isSharedCheck_2250_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_tail_2228_);
lean_inc(v_head_2227_);
lean_dec(v_x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2250_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_before_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2248_; 
v_before_2232_ = lean_ctor_get(v_head_2227_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_head_2227_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_head_2227_, 1);
lean_dec(v_unused_2249_);
v___x_2234_ = v_head_2227_;
v_isShared_2235_ = v_isSharedCheck_2248_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_before_2232_);
lean_dec(v_head_2227_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2248_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 7);
lean_ctor_set(v___x_2234_, 1, v___x_2236_);
lean_ctor_set(v___x_2234_, 0, v_x_2225_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_x_2225_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12___closed__2);
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 7);
lean_ctor_set(v___x_2230_, 1, v___x_2239_);
lean_ctor_set(v___x_2230_, 0, v___x_2238_);
v___x_2241_ = v___x_2230_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = l_Lean_MessageData_ofSyntax(v_before_2232_);
v___x_2243_ = l_Lean_indentD(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2241_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v_x_2225_ = v___x_2244_;
v_x_2226_ = v_tail_2228_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(lean_object* v_opts_2251_, lean_object* v_opt_2252_){
_start:
{
lean_object* v_name_2253_; lean_object* v_defValue_2254_; lean_object* v_map_2255_; lean_object* v___x_2256_; 
v_name_2253_ = lean_ctor_get(v_opt_2252_, 0);
v_defValue_2254_ = lean_ctor_get(v_opt_2252_, 1);
v_map_2255_ = lean_ctor_get(v_opts_2251_, 0);
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2255_, v_name_2253_);
if (lean_obj_tag(v___x_2256_) == 0)
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_unbox(v_defValue_2254_);
return v___x_2257_;
}
else
{
lean_object* v_val_2258_; 
v_val_2258_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v___x_2256_, 1);
if (lean_obj_tag(v_val_2258_) == 1)
{
uint8_t v_v_2259_; 
v_v_2259_ = lean_ctor_get_uint8(v_val_2258_, 0);
lean_dec_ref_known(v_val_2258_, 0);
return v_v_2259_;
}
else
{
uint8_t v___x_2260_; 
lean_dec(v_val_2258_);
v___x_2260_ = lean_unbox(v_defValue_2254_);
return v___x_2260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11___boxed(lean_object* v_opts_2261_, lean_object* v_opt_2262_){
_start:
{
uint8_t v_res_2263_; lean_object* v_r_2264_; 
v_res_2263_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_opts_2261_, v_opt_2262_);
lean_dec_ref(v_opt_2262_);
lean_dec_ref(v_opts_2261_);
v_r_2264_ = lean_box(v_res_2263_);
return v_r_2264_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__1));
v___x_2269_ = l_Lean_MessageData_ofFormat(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(lean_object* v_msgData_2270_, lean_object* v_macroStack_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_options_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_options_2274_ = lean_ctor_get(v___y_2272_, 2);
v___x_2275_ = l_Lean_Elab_pp_macroStack;
v___x_2276_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__11(v_options_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec(v_macroStack_2271_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_msgData_2270_);
return v___x_2277_;
}
else
{
if (lean_obj_tag(v_macroStack_2271_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_msgData_2270_);
return v___x_2278_;
}
else
{
lean_object* v_head_2279_; lean_object* v_after_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2295_; 
v_head_2279_ = lean_ctor_get(v_macroStack_2271_, 0);
lean_inc(v_head_2279_);
v_after_2280_ = lean_ctor_get(v_head_2279_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_head_2279_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v_head_2279_, 0);
lean_dec(v_unused_2296_);
v___x_2282_ = v_head_2279_;
v_isShared_2283_ = v_isSharedCheck_2295_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_after_2280_);
lean_dec(v_head_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2295_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instToMessageData_fmt___closed__9);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 7);
lean_ctor_set(v___x_2282_, 1, v___x_2284_);
lean_ctor_set(v___x_2282_, 0, v_msgData_2270_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_msgData_2270_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_msgData_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2287_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___closed__2);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_ofSyntax(v_after_2280_);
v___x_2290_ = l_Lean_indentD(v___x_2289_);
v_msgData_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2291_, 0, v___x_2288_);
lean_ctor_set(v_msgData_2291_, 1, v___x_2290_);
v___x_2292_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9_spec__12(v_msgData_2291_, v_macroStack_2271_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg___boxed(lean_object* v_msgData_2297_, lean_object* v_macroStack_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_2297_, v_macroStack_2298_, v___y_2299_);
lean_dec_ref(v___y_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(lean_object* v_msg_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_ref_2310_; lean_object* v___x_2311_; lean_object* v_a_2312_; lean_object* v_macroStack_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_ref_2310_ = lean_ctor_get(v___y_2307_, 5);
v___x_2311_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_2302_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v_macroStack_2313_ = lean_ctor_get(v___y_2303_, 1);
v___x_2314_ = l_Lean_Elab_getBetterRef(v_ref_2310_, v_macroStack_2313_);
lean_inc(v_macroStack_2313_);
v___x_2315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_a_2312_, v_macroStack_2313_, v___y_2307_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2314_);
lean_ctor_set(v___x_2320_, 1, v_a_2316_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 1);
lean_ctor_set(v___x_2318_, 0, v___x_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg___boxed(lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__0));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__2));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(lean_object* v_e_2340_, lean_object* v_a_2341_, lean_object* v_00_u03b1_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__0___closed__1);
v___x_2352_ = l_Lean_MessageData_ofExpr(v_e_2340_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__1);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = l_Lean_MessageData_ofExpr(v_a_2341_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___closed__3);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v___x_2359_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3___boxed(lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v_00_u03b1_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2361_, v_a_2362_, v_00_u03b1_2363_, v_x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed(lean_object* v_tail_2373_, lean_object* v_cont_2374_, lean_object* v_g_2375_, lean_object* v_fs_2376_, lean_object* v_clears_2377_, lean_object* v_a_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(v_tail_2373_, v_cont_2374_, v_g_2375_, v_fs_2376_, v_clears_2377_, v_a_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(lean_object* v_e_2388_, lean_object* v_g_2389_, lean_object* v_fs_2390_, lean_object* v_clears_2391_, lean_object* v_a_2392_, lean_object* v_cont_2393_, lean_object* v_ref_2394_, lean_object* v_p_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2403_ = lean_box(0);
lean_inc_ref(v_e_2388_);
v___x_2404_ = l_Lean_Expr_mdata___override(v___x_2403_, v_e_2388_);
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_box(0);
v___x_2407_ = 0;
v___x_2408_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2394_, v___x_2404_, v___x_2405_, v___x_2405_, v___x_2406_, v___x_2407_, v___x_2407_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2409_; 
lean_dec_ref_known(v___x_2408_, 1);
v___x_2409_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2389_, v_fs_2390_, v_clears_2391_, v_e_2388_, v_a_2392_, v_p_2395_, v_cont_2393_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec_ref(v_e_2388_);
return v___x_2409_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_p_2395_);
lean_dec_ref(v_cont_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_clears_2391_);
lean_dec(v_fs_2390_);
lean_dec(v_g_2389_);
lean_dec_ref(v_e_2388_);
v_a_2410_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2408_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed(lean_object* v_e_2418_, lean_object* v_g_2419_, lean_object* v_fs_2420_, lean_object* v_clears_2421_, lean_object* v_a_2422_, lean_object* v_cont_2423_, lean_object* v_ref_2424_, lean_object* v_p_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2(v_e_2418_, v_g_2419_, v_fs_2420_, v_clears_2421_, v_a_2422_, v_cont_2423_, v_ref_2424_, v_p_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(lean_object* v_fs_2434_, lean_object* v_clears_2435_, lean_object* v_cont_2436_, lean_object* v_a_2437_, lean_object* v_goal_2438_, lean_object* v_ctorName_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
if (lean_obj_tag(v_a_2440_) == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec_ref(v_goal_2438_);
lean_dec_ref(v_cont_2436_);
lean_dec_ref(v_clears_2435_);
lean_dec(v_fs_2434_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2440_);
lean_ctor_set(v___x_2448_, 1, v_a_2437_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
else
{
lean_object* v_head_2450_; lean_object* v_tail_2451_; lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2486_; 
v_head_2450_ = lean_ctor_get(v_a_2440_, 0);
lean_inc(v_head_2450_);
v_tail_2451_ = lean_ctor_get(v_a_2440_, 1);
lean_inc(v_tail_2451_);
lean_dec_ref_known(v_a_2440_, 2);
v_fst_2452_ = lean_ctor_get(v_head_2450_, 0);
v_snd_2453_ = lean_ctor_get(v_head_2450_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_head_2450_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2455_ = v_head_2450_;
v_isShared_2456_ = v_isSharedCheck_2486_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2453_);
lean_inc(v_fst_2452_);
lean_dec(v_head_2450_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2486_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_fst_2452_);
v___x_2458_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align_spec__0(v___x_2457_, v_ctorName_2439_);
lean_dec_ref_known(v___x_2457_, 1);
if (v___x_2458_ == 0)
{
lean_del_object(v___x_2455_);
lean_dec(v_snd_2453_);
v_a_2440_ = v_tail_2451_;
goto _start;
}
else
{
lean_object* v_mvarId_2460_; lean_object* v_fields_2461_; lean_object* v_subst_2462_; lean_object* v_fs_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_mvarId_2460_ = lean_ctor_get(v_goal_2438_, 0);
lean_inc(v_mvarId_2460_);
v_fields_2461_ = lean_ctor_get(v_goal_2438_, 1);
lean_inc_ref(v_fields_2461_);
v_subst_2462_ = lean_ctor_get(v_goal_2438_, 2);
lean_inc(v_subst_2462_);
lean_dec_ref(v_goal_2438_);
v_fs_2463_ = l_Lean_Meta_FVarSubst_append(v_fs_2434_, v_subst_2462_);
v___x_2464_ = lean_array_to_list(v_fields_2461_);
v___x_2465_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_snd_2453_, v___x_2464_);
v___x_2466_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_mvarId_2460_, v_fs_2463_, v_clears_2435_, v_a_2437_, v___x_2465_, v_cont_2436_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2477_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v_a_2467_);
lean_ctor_set(v___x_2455_, 0, v_tail_2451_);
v___x_2472_ = v___x_2455_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_tail_2451_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2472_);
v___x_2474_ = v___x_2469_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
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
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_del_object(v___x_2455_);
lean_dec(v_tail_2451_);
v_a_2478_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2466_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2466_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(lean_object* v_fs_2487_, lean_object* v_clears_2488_, lean_object* v_cont_2489_, lean_object* v_as_2490_, size_t v_i_2491_, size_t v_stop_2492_, lean_object* v_b_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_usize_dec_eq(v_i_2491_, v_stop_2492_);
if (v___x_2501_ == 0)
{
lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___x_2504_; lean_object* v_toInductionSubgoal_2505_; lean_object* v_ctorName_2506_; lean_object* v___x_2507_; 
v_fst_2502_ = lean_ctor_get(v_b_2493_, 0);
lean_inc(v_fst_2502_);
v_snd_2503_ = lean_ctor_get(v_b_2493_, 1);
lean_inc(v_snd_2503_);
lean_dec_ref(v_b_2493_);
v___x_2504_ = lean_array_uget_borrowed(v_as_2490_, v_i_2491_);
v_toInductionSubgoal_2505_ = lean_ctor_get(v___x_2504_, 0);
v_ctorName_2506_ = lean_ctor_get(v___x_2504_, 1);
lean_inc_ref(v_toInductionSubgoal_2505_);
lean_inc_ref(v_cont_2489_);
lean_inc_ref(v_clears_2488_);
lean_inc(v_fs_2487_);
v___x_2507_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_2487_, v_clears_2488_, v_cont_2489_, v_snd_2503_, v_toInductionSubgoal_2505_, v_ctorName_2506_, v_fst_2502_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; size_t v___x_2509_; size_t v___x_2510_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2491_, v___x_2509_);
v_i_2491_ = v___x_2510_;
v_b_2493_ = v_a_2508_;
goto _start;
}
else
{
lean_dec_ref(v_cont_2489_);
lean_dec_ref(v_clears_2488_);
lean_dec(v_fs_2487_);
return v___x_2507_;
}
}
else
{
lean_object* v___x_2512_; 
lean_dec_ref(v_cont_2489_);
lean_dec_ref(v_clears_2488_);
lean_dec(v_fs_2487_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_b_2493_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(lean_object* v_e_2515_, lean_object* v___y_2516_, lean_object* v_asFVar_2517_, lean_object* v_a_2518_, lean_object* v_fs_2519_, lean_object* v_clears_2520_, lean_object* v_cont_2521_, lean_object* v___x_2522_, lean_object* v_g_2523_, lean_object* v___x_2524_, lean_object* v_pat_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___y_2535_; lean_object* v_fst_2554_; lean_object* v_snd_2555_; lean_object* v___y_2570_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2582_ = lean_box(0);
lean_inc_ref(v_e_2515_);
v___x_2583_ = l_Lean_Expr_mdata___override(v___x_2582_, v_e_2515_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_box(0);
v___x_2586_ = 0;
lean_inc(v___y_2516_);
v___x_2587_ = l_Lean_Elab_Term_addTermInfo_x27(v___y_2516_, v___x_2583_, v___x_2584_, v___x_2584_, v___x_2585_, v___x_2586_, v___x_2586_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref_known(v___x_2587_, 1);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc_ref(v_e_2515_);
v___x_2588_ = lean_apply_6(v_asFVar_2517_, v_e_2515_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref_known(v___x_2588_, 1);
v___x_2589_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2586_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2589_, 1);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc_ref(v_e_2515_);
v___x_2590_ = lean_infer_type(v_e_2515_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = l_Lean_Meta_whnfD(v_a_2591_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_Expr_getAppFn(v_a_2593_);
if (lean_obj_tag(v___x_2594_) == 4)
{
lean_object* v_declName_2595_; lean_object* v___x_2596_; lean_object* v_env_2597_; lean_object* v___x_2598_; 
v_declName_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_declName_2595_);
lean_dec_ref_known(v___x_2594_, 2);
v___x_2596_ = lean_st_ref_get(v___y_2532_);
v_env_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_env_2597_);
lean_dec(v___x_2596_);
v___x_2598_ = l_Lean_Environment_find_x3f(v_env_2597_, v_declName_2595_, v___x_2586_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec(v___y_2516_);
v___x_2599_ = lean_box(0);
v___x_2600_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2515_, v_a_2593_, lean_box(0), v___x_2599_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v___y_2570_ = v___x_2600_;
goto v___jp_2569_;
}
else
{
lean_object* v_val_2601_; 
v_val_2601_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v___x_2598_, 1);
switch(lean_obj_tag(v_val_2601_))
{
case 4:
{
lean_object* v_val_2602_; uint8_t v_kind_2603_; 
lean_dec(v___y_2516_);
v_val_2602_ = lean_ctor_get(v_val_2601_, 0);
lean_inc_ref(v_val_2602_);
lean_dec_ref_known(v_val_2601_, 1);
v_kind_2603_ = lean_ctor_get_uint8(v_val_2602_, sizeof(void*)*1);
lean_dec_ref(v_val_2602_);
if (v_kind_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec(v_a_2593_);
v___x_2604_ = lean_box(0);
lean_inc(v_fs_2519_);
v___x_2605_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2586_, v_e_2515_, v___x_2522_, v_g_2523_, v___x_2524_, v_fs_2519_, v_pat_2525_, v___x_2604_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v___y_2570_ = v___x_2605_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_box(0);
lean_inc_ref(v_e_2515_);
v___x_2607_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2515_, v_a_2593_, lean_box(0), v___x_2606_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
lean_inc(v_fs_2519_);
v___x_2609_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5(v___x_2586_, v_e_2515_, v___x_2522_, v_g_2523_, v___x_2524_, v_fs_2519_, v_pat_2525_, v_a_2608_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v___y_2570_ = v___x_2609_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_e_2515_);
v_a_2610_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2607_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2607_);
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
}
case 5:
{
lean_object* v_val_2618_; lean_object* v_numParams_2619_; lean_object* v_ctors_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec(v_a_2593_);
lean_dec_ref(v___x_2524_);
lean_dec(v___x_2522_);
v_val_2618_ = lean_ctor_get(v_val_2601_, 0);
lean_inc_ref(v_val_2618_);
lean_dec_ref_known(v_val_2601_, 1);
v_numParams_2619_ = lean_ctor_get(v_val_2618_, 1);
lean_inc(v_numParams_2619_);
v_ctors_2620_ = lean_ctor_get(v_val_2618_, 4);
lean_inc(v_ctors_2620_);
lean_dec_ref(v_val_2618_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___closed__0));
v___x_2622_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asAlts(v_pat_2525_);
v___x_2623_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors(v___y_2516_, v_numParams_2619_, v___x_2621_, v_ctors_2620_, v___x_2622_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v_numParams_2619_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v_fst_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_a_2624_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_a_2624_);
v___x_2627_ = l_Lean_Expr_fvarId_x21(v_e_2515_);
lean_dec_ref(v_e_2515_);
v___x_2628_ = 1;
v___x_2629_ = l_Lean_MVarId_cases(v_g_2523_, v___x_2627_, v_fst_2625_, v___x_2628_, v___x_2584_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v_fst_2554_ = v_snd_2626_;
v_snd_2555_ = v_a_2630_;
goto v___jp_2553_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_snd_2626_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
v_a_2631_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2629_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2629_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_g_2523_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_e_2515_);
v_a_2639_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2623_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2623_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
default: 
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec(v_val_2601_);
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec(v___y_2516_);
v___x_2647_ = lean_box(0);
v___x_2648_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2515_, v_a_2593_, lean_box(0), v___x_2647_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v___y_2570_ = v___x_2648_;
goto v___jp_2569_;
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v___x_2594_);
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec(v___y_2516_);
v___x_2649_ = lean_box(0);
v___x_2650_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__3(v_e_2515_, v_a_2593_, lean_box(0), v___x_2649_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v___y_2570_ = v___x_2650_;
goto v___jp_2569_;
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec(v___y_2516_);
lean_dec_ref(v_e_2515_);
v_a_2651_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2592_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2592_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec(v___y_2516_);
lean_dec_ref(v_e_2515_);
v_a_2659_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2590_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2590_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec(v___y_2516_);
lean_dec_ref(v_e_2515_);
v_a_2667_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2589_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2589_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec(v___y_2516_);
lean_dec_ref(v_e_2515_);
v_a_2675_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2588_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2588_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_pat_2525_);
lean_dec_ref(v___x_2524_);
lean_dec(v_g_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_asFVar_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v_e_2515_);
v_a_2683_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2587_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2587_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
v___jp_2534_:
{
if (lean_obj_tag(v___y_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
v_a_2536_ = lean_ctor_get(v___y_2535_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___y_2535_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v___y_2535_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___y_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_snd_2540_; lean_object* v___x_2542_; 
v_snd_2540_ = lean_ctor_get(v_a_2536_, 1);
lean_inc(v_snd_2540_);
lean_dec(v_a_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v_snd_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_snd_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___y_2535_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___y_2535_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___y_2535_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___y_2535_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = lean_array_get_size(v_snd_2555_);
v___x_2558_ = lean_nat_dec_lt(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
lean_dec_ref(v_snd_2555_);
lean_dec(v_fst_2554_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_a_2518_);
return v___x_2559_;
}
else
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
lean_inc(v_a_2518_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_fst_2554_);
lean_ctor_set(v___x_2560_, 1, v_a_2518_);
v___x_2561_ = lean_nat_dec_le(v___x_2557_, v___x_2557_);
if (v___x_2561_ == 0)
{
if (v___x_2558_ == 0)
{
lean_object* v___x_2562_; 
lean_dec_ref_known(v___x_2560_, 2);
lean_dec_ref(v_snd_2555_);
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_a_2518_);
return v___x_2562_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_a_2518_);
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2557_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2519_, v_clears_2520_, v_cont_2521_, v_snd_2555_, v___x_2563_, v___x_2564_, v___x_2560_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v_snd_2555_);
v___y_2535_ = v___x_2565_;
goto v___jp_2534_;
}
}
else
{
size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_a_2518_);
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2557_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_2519_, v_clears_2520_, v_cont_2521_, v_snd_2555_, v___x_2566_, v___x_2567_, v___x_2560_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v_snd_2555_);
v___y_2535_ = v___x_2568_;
goto v___jp_2534_;
}
}
}
v___jp_2569_:
{
if (lean_obj_tag(v___y_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v_fst_2572_; lean_object* v_snd_2573_; 
v_a_2571_ = lean_ctor_get(v___y_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___y_2570_, 1);
v_fst_2572_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_fst_2572_);
v_snd_2573_ = lean_ctor_get(v_a_2571_, 1);
lean_inc(v_snd_2573_);
lean_dec(v_a_2571_);
v_fst_2554_ = v_fst_2572_;
v_snd_2555_ = v_snd_2573_;
goto v___jp_2553_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_cont_2521_);
lean_dec_ref(v_clears_2520_);
lean_dec(v_fs_2519_);
lean_dec(v_a_2518_);
v_a_2574_ = lean_ctor_get(v___y_2570_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___y_2570_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___y_2570_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___y_2570_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_e_2691_ = _args[0];
lean_object* v___y_2692_ = _args[1];
lean_object* v_asFVar_2693_ = _args[2];
lean_object* v_a_2694_ = _args[3];
lean_object* v_fs_2695_ = _args[4];
lean_object* v_clears_2696_ = _args[5];
lean_object* v_cont_2697_ = _args[6];
lean_object* v___x_2698_ = _args[7];
lean_object* v_g_2699_ = _args[8];
lean_object* v___x_2700_ = _args[9];
lean_object* v_pat_2701_ = _args[10];
lean_object* v_x_2702_ = _args[11];
lean_object* v___y_2703_ = _args[12];
lean_object* v___y_2704_ = _args[13];
lean_object* v___y_2705_ = _args[14];
lean_object* v___y_2706_ = _args[15];
lean_object* v___y_2707_ = _args[16];
lean_object* v___y_2708_ = _args[17];
lean_object* v___y_2709_ = _args[18];
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6(v_e_2691_, v___y_2692_, v_asFVar_2693_, v_a_2694_, v_fs_2695_, v_clears_2696_, v_cont_2697_, v___x_2698_, v_g_2699_, v___x_2700_, v_pat_2701_, v_x_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v_x_2702_);
return v_res_2710_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__1));
v___x_2715_ = l_Lean_MessageData_ofFormat(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__2);
v___x_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(lean_object* v_pat_2718_, lean_object* v___f_2719_, lean_object* v_e_2720_, lean_object* v_asFVar_2721_, lean_object* v_g_2722_, lean_object* v_fs_2723_, lean_object* v_cont_2724_, lean_object* v_clears_2725_, lean_object* v_a_2726_, lean_object* v___f_2727_, lean_object* v___f_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
switch(lean_obj_tag(v_pat_2718_))
{
case 1:
{
lean_object* v_a_2736_; 
lean_dec_ref(v___f_2728_);
lean_dec_ref(v___f_2727_);
v_a_2736_ = lean_ctor_get(v_pat_2718_, 1);
lean_inc(v_a_2736_);
if (lean_obj_tag(v_a_2736_) == 1)
{
lean_object* v_pre_2737_; 
v_pre_2737_ = lean_ctor_get(v_a_2736_, 0);
if (lean_obj_tag(v_pre_2737_) == 0)
{
lean_object* v_ref_2738_; lean_object* v_str_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v_ref_2738_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2738_);
lean_dec_ref_known(v_pat_2718_, 2);
v_str_2739_ = lean_ctor_get(v_a_2736_, 1);
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f___closed__0));
v___x_2741_ = lean_string_dec_eq(v_str_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2742_ = lean_apply_9(v___f_2719_, v_ref_2738_, v_a_2736_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2742_;
}
else
{
uint8_t v___x_2743_; lean_object* v___x_2744_; 
lean_inc(v_pre_2737_);
lean_dec_ref_known(v_a_2736_, 2);
lean_dec_ref(v___f_2719_);
v___x_2743_ = 0;
v___x_2744_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2743_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec_ref_known(v___x_2744_, 1);
v___x_2745_ = lean_box(0);
lean_inc_ref(v_e_2720_);
v___x_2746_ = l_Lean_Expr_mdata___override(v___x_2745_, v_e_2720_);
v___x_2747_ = lean_box(0);
v___x_2748_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2738_, v___x_2746_, v___x_2747_, v___x_2747_, v_pre_2737_, v___x_2743_, v___x_2743_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
lean_dec_ref_known(v___x_2748_, 1);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2749_ = lean_apply_6(v_asFVar_2721_, v_e_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l_Lean_Meta_substEq(v_g_2722_, v_a_2750_, v_fs_2723_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v_fst_2753_; lean_object* v_snd_2754_; lean_object* v___x_2755_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
v_fst_2753_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_fst_2753_);
v_snd_2754_ = lean_ctor_get(v_a_2752_, 1);
lean_inc(v_snd_2754_);
lean_dec(v_a_2752_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2755_ = lean_apply_11(v_cont_2724_, v_snd_2754_, v_fst_2753_, v_clears_2725_, v_a_2726_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2755_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
v_a_2756_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2751_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
v_a_2764_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2749_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2749_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
v_a_2772_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2748_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2748_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_ref_2738_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
v_a_2780_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2744_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2744_);
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
}
else
{
lean_object* v_ref_2788_; lean_object* v___x_2789_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
v_ref_2788_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2788_);
lean_dec_ref_known(v_pat_2718_, 2);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2789_ = lean_apply_9(v___f_2719_, v_ref_2788_, v_a_2736_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2789_;
}
}
else
{
lean_object* v_ref_2790_; lean_object* v___x_2791_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
v_ref_2790_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2790_);
lean_dec_ref_known(v_pat_2718_, 2);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2791_ = lean_apply_9(v___f_2719_, v_ref_2790_, v_a_2736_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2791_;
}
}
case 2:
{
lean_object* v_ref_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v___f_2728_);
lean_dec_ref(v___f_2727_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v___f_2719_);
v_ref_2792_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2792_);
lean_dec_ref_known(v_pat_2718_, 1);
v___x_2793_ = lean_box(0);
lean_inc_ref(v_e_2720_);
v___x_2794_ = l_Lean_Expr_mdata___override(v___x_2793_, v_e_2720_);
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_box(0);
v___x_2797_ = 0;
v___x_2798_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2792_, v___x_2794_, v___x_2795_, v___x_2795_, v___x_2796_, v___x_2797_, v___x_2797_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_dec_ref_known(v___x_2798_, 1);
if (lean_obj_tag(v_e_2720_) == 1)
{
lean_object* v_fvarId_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_fvarId_2799_ = lean_ctor_get(v_e_2720_, 0);
lean_inc(v_fvarId_2799_);
lean_dec_ref_known(v_e_2720_, 1);
v___x_2800_ = lean_array_push(v_clears_2725_, v_fvarId_2799_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2801_ = lean_apply_11(v_cont_2724_, v_g_2722_, v_fs_2723_, v___x_2800_, v_a_2726_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v_e_2720_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2802_ = lean_apply_11(v_cont_2724_, v_g_2722_, v_fs_2723_, v_clears_2725_, v_a_2726_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2802_;
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2803_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2798_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2798_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
case 4:
{
lean_object* v_ref_2811_; lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v___f_2728_);
lean_dec_ref(v___f_2727_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v___f_2719_);
v_ref_2811_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2811_);
v_a_2812_ = lean_ctor_get(v_pat_2718_, 1);
lean_inc_ref(v_a_2812_);
v_a_2813_ = lean_ctor_get(v_pat_2718_, 2);
lean_inc(v_a_2813_);
lean_dec_ref_known(v_pat_2718_, 3);
v___x_2814_ = lean_box(0);
lean_inc_ref(v_e_2720_);
v___x_2815_ = l_Lean_Expr_mdata___override(v___x_2814_, v_e_2720_);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_box(0);
v___x_2818_ = 0;
v___x_2819_ = l_Lean_Elab_Term_addTermInfo_x27(v_ref_2811_, v___x_2815_, v___x_2816_, v___x_2816_, v___x_2817_, v___x_2818_, v___x_2818_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2820_; 
lean_dec_ref_known(v___x_2819_, 1);
v___x_2820_ = l_Lean_Elab_Term_elabType(v_a_2813_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___x_2842_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc_ref(v_e_2720_);
v___x_2842_ = lean_infer_type(v_e_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc_n(v_a_2843_, 2);
lean_dec_ref_known(v___x_2842_, 1);
lean_inc(v_a_2821_);
v___x_2844_ = l_Lean_Meta_isExprDefEq(v_a_2843_, v_a_2821_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; uint8_t v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = lean_unbox(v_a_2845_);
lean_dec(v_a_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___closed__3);
lean_inc_ref(v_e_2720_);
lean_inc(v_a_2821_);
v___x_2848_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_2847_, v_a_2821_, v_a_2843_, v_e_2720_, v___x_2816_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_dec_ref_known(v___x_2848_, 1);
v___y_2823_ = v___y_2729_;
v___y_2824_ = v___y_2730_;
v___y_2825_ = v___y_2731_;
v___y_2826_ = v___y_2732_;
v___y_2827_ = v___y_2733_;
v___y_2828_ = v___y_2734_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_dec(v_a_2843_);
v___y_2823_ = v___y_2729_;
v___y_2824_ = v___y_2730_;
v___y_2825_ = v___y_2731_;
v___y_2826_ = v___y_2732_;
v___y_2827_ = v___y_2733_;
v___y_2828_ = v___y_2734_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_a_2843_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2857_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2844_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2844_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2865_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2842_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2842_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
v___jp_2822_:
{
if (lean_obj_tag(v_e_2720_) == 1)
{
lean_object* v_fvarId_2829_; lean_object* v___x_2830_; 
v_fvarId_2829_ = lean_ctor_get(v_e_2720_, 0);
lean_inc(v_fvarId_2829_);
v___x_2830_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_g_2722_, v_fvarId_2829_, v_a_2821_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_a_2831_, v_fs_2723_, v_clears_2725_, v_e_2720_, v_a_2726_, v_a_2812_, v_cont_2724_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref_known(v_e_2720_, 1);
return v___x_2832_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec_ref_known(v_e_2720_, 1);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
v_a_2833_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2830_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2830_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v___x_2841_; 
lean_dec(v_a_2821_);
v___x_2841_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2722_, v_fs_2723_, v_clears_2725_, v_e_2720_, v_a_2726_, v_a_2812_, v_cont_2724_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref(v_e_2720_);
return v___x_2841_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2873_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2820_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2820_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_e_2720_);
v_a_2881_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2819_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2819_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
case 0:
{
lean_object* v_ref_2889_; lean_object* v_a_2890_; lean_object* v___x_2891_; 
lean_dec_ref(v___f_2728_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
lean_dec_ref(v___f_2719_);
v_ref_2889_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2889_);
v_a_2890_ = lean_ctor_get(v_pat_2718_, 1);
lean_inc_ref(v_a_2890_);
lean_dec_ref_known(v_pat_2718_, 2);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2891_ = lean_apply_9(v___f_2727_, v_ref_2889_, v_a_2890_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2891_;
}
case 6:
{
lean_object* v_a_2892_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
lean_dec_ref(v___f_2719_);
v_a_2892_ = lean_ctor_get(v_pat_2718_, 1);
if (lean_obj_tag(v_a_2892_) == 1)
{
lean_object* v_tail_2893_; 
v_tail_2893_ = lean_ctor_get(v_a_2892_, 1);
if (lean_obj_tag(v_tail_2893_) == 0)
{
lean_object* v_ref_2894_; lean_object* v_head_2895_; lean_object* v___x_2896_; 
lean_inc_ref(v_a_2892_);
lean_dec_ref(v___f_2728_);
v_ref_2894_ = lean_ctor_get(v_pat_2718_, 0);
lean_inc(v_ref_2894_);
lean_dec_ref_known(v_pat_2718_, 2);
v_head_2895_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_head_2895_);
lean_dec_ref_known(v_a_2892_, 2);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2896_ = lean_apply_9(v___f_2727_, v_ref_2894_, v_head_2895_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; 
lean_dec_ref(v___f_2727_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2897_ = lean_apply_8(v___f_2728_, v_pat_2718_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2897_;
}
}
else
{
lean_object* v___x_2898_; 
lean_dec_ref(v___f_2727_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2898_ = lean_apply_8(v___f_2728_, v_pat_2718_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2898_;
}
}
default: 
{
lean_object* v___x_2899_; 
lean_dec_ref(v___f_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_clears_2725_);
lean_dec_ref(v_cont_2724_);
lean_dec(v_fs_2723_);
lean_dec(v_g_2722_);
lean_dec_ref(v_asFVar_2721_);
lean_dec_ref(v_e_2720_);
lean_dec_ref(v___f_2719_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
v___x_2899_ = lean_apply_8(v___f_2728_, v_pat_2718_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_pat_2900_ = _args[0];
lean_object* v___f_2901_ = _args[1];
lean_object* v_e_2902_ = _args[2];
lean_object* v_asFVar_2903_ = _args[3];
lean_object* v_g_2904_ = _args[4];
lean_object* v_fs_2905_ = _args[5];
lean_object* v_cont_2906_ = _args[6];
lean_object* v_clears_2907_ = _args[7];
lean_object* v_a_2908_ = _args[8];
lean_object* v___f_2909_ = _args[9];
lean_object* v___f_2910_ = _args[10];
lean_object* v___y_2911_ = _args[11];
lean_object* v___y_2912_ = _args[12];
lean_object* v___y_2913_ = _args[13];
lean_object* v___y_2914_ = _args[14];
lean_object* v___y_2915_ = _args[15];
lean_object* v___y_2916_ = _args[16];
lean_object* v___y_2917_ = _args[17];
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7(v_pat_2900_, v___f_2901_, v_e_2902_, v_asFVar_2903_, v_g_2904_, v_fs_2905_, v_cont_2906_, v_clears_2907_, v_a_2908_, v___f_2909_, v___f_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(lean_object* v_g_2919_, lean_object* v_fs_2920_, lean_object* v_clears_2921_, lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_pat_2924_, lean_object* v_cont_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_asFVar_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v_e_2936_; lean_object* v___f_2937_; lean_object* v___f_2938_; lean_object* v___y_2940_; lean_object* v_ref_2962_; 
v_asFVar_2933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___closed__0));
v___x_2934_ = lean_box(1);
v___x_2935_ = l_Lean_instInhabitedExpr;
lean_inc_n(v_fs_2920_, 3);
v_e_2936_ = l_Lean_Meta_FVarSubst_apply(v_fs_2920_, v_e_2922_);
lean_inc_n(v_a_2923_, 2);
lean_inc_ref_n(v_clears_2921_, 2);
lean_inc_n(v_g_2919_, 2);
lean_inc_ref_n(v_cont_2925_, 2);
lean_inc_ref_n(v_e_2936_, 2);
v___f_2937_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_2937_, 0, v_e_2936_);
lean_closure_set(v___f_2937_, 1, v_cont_2925_);
lean_closure_set(v___f_2937_, 2, v_g_2919_);
lean_closure_set(v___f_2937_, 3, v_fs_2920_);
lean_closure_set(v___f_2937_, 4, v_clears_2921_);
lean_closure_set(v___f_2937_, 5, v_a_2923_);
v___f_2938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__2___boxed), 15, 6);
lean_closure_set(v___f_2938_, 0, v_e_2936_);
lean_closure_set(v___f_2938_, 1, v_g_2919_);
lean_closure_set(v___f_2938_, 2, v_fs_2920_);
lean_closure_set(v___f_2938_, 3, v_clears_2921_);
lean_closure_set(v___f_2938_, 4, v_a_2923_);
lean_closure_set(v___f_2938_, 5, v_cont_2925_);
v_ref_2962_ = lean_ctor_get(v_pat_2924_, 0);
lean_inc(v_ref_2962_);
v___y_2940_ = v_ref_2962_;
goto v___jp_2939_;
v___jp_2939_:
{
lean_object* v_fileName_2941_; lean_object* v_fileMap_2942_; lean_object* v_options_2943_; lean_object* v_currRecDepth_2944_; lean_object* v_maxRecDepth_2945_; lean_object* v_ref_2946_; lean_object* v_currNamespace_2947_; lean_object* v_openDecls_2948_; lean_object* v_initHeartbeats_2949_; lean_object* v_maxHeartbeats_2950_; lean_object* v_quotContext_2951_; lean_object* v_currMacroScope_2952_; uint8_t v_diag_2953_; lean_object* v_cancelTk_x3f_2954_; uint8_t v_suppressElabErrors_2955_; lean_object* v_inheritedTraceOptions_2956_; lean_object* v___f_2957_; lean_object* v___y_2958_; lean_object* v_ref_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_fileName_2941_ = lean_ctor_get(v_a_2930_, 0);
v_fileMap_2942_ = lean_ctor_get(v_a_2930_, 1);
v_options_2943_ = lean_ctor_get(v_a_2930_, 2);
v_currRecDepth_2944_ = lean_ctor_get(v_a_2930_, 3);
v_maxRecDepth_2945_ = lean_ctor_get(v_a_2930_, 4);
v_ref_2946_ = lean_ctor_get(v_a_2930_, 5);
v_currNamespace_2947_ = lean_ctor_get(v_a_2930_, 6);
v_openDecls_2948_ = lean_ctor_get(v_a_2930_, 7);
v_initHeartbeats_2949_ = lean_ctor_get(v_a_2930_, 8);
v_maxHeartbeats_2950_ = lean_ctor_get(v_a_2930_, 9);
v_quotContext_2951_ = lean_ctor_get(v_a_2930_, 10);
v_currMacroScope_2952_ = lean_ctor_get(v_a_2930_, 11);
v_diag_2953_ = lean_ctor_get_uint8(v_a_2930_, sizeof(void*)*14);
v_cancelTk_x3f_2954_ = lean_ctor_get(v_a_2930_, 12);
v_suppressElabErrors_2955_ = lean_ctor_get_uint8(v_a_2930_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2956_ = lean_ctor_get(v_a_2930_, 13);
lean_inc_ref(v_pat_2924_);
lean_inc_n(v_g_2919_, 2);
lean_inc_ref(v_cont_2925_);
lean_inc_ref(v_clears_2921_);
lean_inc(v_fs_2920_);
lean_inc(v_a_2923_);
lean_inc(v___y_2940_);
lean_inc_ref(v_e_2936_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__6___boxed), 19, 11);
lean_closure_set(v___f_2957_, 0, v_e_2936_);
lean_closure_set(v___f_2957_, 1, v___y_2940_);
lean_closure_set(v___f_2957_, 2, v_asFVar_2933_);
lean_closure_set(v___f_2957_, 3, v_a_2923_);
lean_closure_set(v___f_2957_, 4, v_fs_2920_);
lean_closure_set(v___f_2957_, 5, v_clears_2921_);
lean_closure_set(v___f_2957_, 6, v_cont_2925_);
lean_closure_set(v___f_2957_, 7, v___x_2934_);
lean_closure_set(v___f_2957_, 8, v_g_2919_);
lean_closure_set(v___f_2957_, 9, v___x_2935_);
lean_closure_set(v___f_2957_, 10, v_pat_2924_);
v___y_2958_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__7___boxed), 18, 11);
lean_closure_set(v___y_2958_, 0, v_pat_2924_);
lean_closure_set(v___y_2958_, 1, v___f_2937_);
lean_closure_set(v___y_2958_, 2, v_e_2936_);
lean_closure_set(v___y_2958_, 3, v_asFVar_2933_);
lean_closure_set(v___y_2958_, 4, v_g_2919_);
lean_closure_set(v___y_2958_, 5, v_fs_2920_);
lean_closure_set(v___y_2958_, 6, v_cont_2925_);
lean_closure_set(v___y_2958_, 7, v_clears_2921_);
lean_closure_set(v___y_2958_, 8, v_a_2923_);
lean_closure_set(v___y_2958_, 9, v___f_2938_);
lean_closure_set(v___y_2958_, 10, v___f_2957_);
v_ref_2959_ = l_Lean_replaceRef(v___y_2940_, v_ref_2946_);
lean_dec(v___y_2940_);
lean_inc_ref(v_inheritedTraceOptions_2956_);
lean_inc(v_cancelTk_x3f_2954_);
lean_inc(v_currMacroScope_2952_);
lean_inc(v_quotContext_2951_);
lean_inc(v_maxHeartbeats_2950_);
lean_inc(v_initHeartbeats_2949_);
lean_inc(v_openDecls_2948_);
lean_inc(v_currNamespace_2947_);
lean_inc(v_maxRecDepth_2945_);
lean_inc(v_currRecDepth_2944_);
lean_inc_ref(v_options_2943_);
lean_inc_ref(v_fileMap_2942_);
lean_inc_ref(v_fileName_2941_);
v___x_2960_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2960_, 0, v_fileName_2941_);
lean_ctor_set(v___x_2960_, 1, v_fileMap_2942_);
lean_ctor_set(v___x_2960_, 2, v_options_2943_);
lean_ctor_set(v___x_2960_, 3, v_currRecDepth_2944_);
lean_ctor_set(v___x_2960_, 4, v_maxRecDepth_2945_);
lean_ctor_set(v___x_2960_, 5, v_ref_2959_);
lean_ctor_set(v___x_2960_, 6, v_currNamespace_2947_);
lean_ctor_set(v___x_2960_, 7, v_openDecls_2948_);
lean_ctor_set(v___x_2960_, 8, v_initHeartbeats_2949_);
lean_ctor_set(v___x_2960_, 9, v_maxHeartbeats_2950_);
lean_ctor_set(v___x_2960_, 10, v_quotContext_2951_);
lean_ctor_set(v___x_2960_, 11, v_currMacroScope_2952_);
lean_ctor_set(v___x_2960_, 12, v_cancelTk_x3f_2954_);
lean_ctor_set(v___x_2960_, 13, v_inheritedTraceOptions_2956_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*14, v_diag_2953_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*14 + 1, v_suppressElabErrors_2955_);
v___x_2961_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_2919_, v___y_2958_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v___x_2960_, v_a_2931_);
lean_dec_ref_known(v___x_2960_, 14);
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(lean_object* v_g_2963_, lean_object* v_fs_2964_, lean_object* v_clears_2965_, lean_object* v_a_2966_, lean_object* v_pats_2967_, lean_object* v_cont_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
if (lean_obj_tag(v_pats_2967_) == 0)
{
lean_object* v___x_2976_; 
lean_inc(v_a_2974_);
lean_inc_ref(v_a_2973_);
lean_inc(v_a_2972_);
lean_inc_ref(v_a_2971_);
lean_inc(v_a_2970_);
lean_inc_ref(v_a_2969_);
v___x_2976_ = lean_apply_11(v_cont_2968_, v_g_2963_, v_fs_2964_, v_clears_2965_, v_a_2966_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, lean_box(0));
return v___x_2976_;
}
else
{
lean_object* v_head_2977_; lean_object* v_tail_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; 
v_head_2977_ = lean_ctor_get(v_pats_2967_, 0);
lean_inc(v_head_2977_);
v_tail_2978_ = lean_ctor_get(v_pats_2967_, 1);
lean_inc(v_tail_2978_);
lean_dec_ref_known(v_pats_2967_, 2);
v_fst_2979_ = lean_ctor_get(v_head_2977_, 0);
lean_inc(v_fst_2979_);
v_snd_2980_ = lean_ctor_get(v_head_2977_, 1);
lean_inc(v_snd_2980_);
lean_dec(v_head_2977_);
v___f_2981_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2981_, 0, v_tail_2978_);
lean_closure_set(v___f_2981_, 1, v_cont_2968_);
v___x_2982_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_2963_, v_fs_2964_, v_clears_2965_, v_snd_2980_, v_a_2966_, v_fst_2979_, v___f_2981_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
lean_dec(v_snd_2980_);
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___lam__0(lean_object* v_tail_2983_, lean_object* v_cont_2984_, lean_object* v_g_2985_, lean_object* v_fs_2986_, lean_object* v_clears_2987_, lean_object* v_a_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2985_, v_fs_2986_, v_clears_2987_, v_a_2988_, v_tail_2983_, v_cont_2984_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg___boxed(lean_object* v_g_2997_, lean_object* v_fs_2998_, lean_object* v_clears_2999_, lean_object* v_a_3000_, lean_object* v_pats_3001_, lean_object* v_cont_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_2997_, v_fs_2998_, v_clears_2999_, v_a_3000_, v_pats_3001_, v_cont_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg___boxed(lean_object* v_fs_3011_, lean_object* v_clears_3012_, lean_object* v_cont_3013_, lean_object* v_as_3014_, lean_object* v_i_3015_, lean_object* v_stop_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
size_t v_i_boxed_3025_; size_t v_stop_boxed_3026_; lean_object* v_res_3027_; 
v_i_boxed_3025_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_stop_boxed_3026_ = lean_unbox_usize(v_stop_3016_);
lean_dec(v_stop_3016_);
v_res_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3011_, v_clears_3012_, v_cont_3013_, v_as_3014_, v_i_boxed_3025_, v_stop_boxed_3026_, v_b_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec_ref(v_as_3014_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg___boxed(lean_object* v_fs_3028_, lean_object* v_clears_3029_, lean_object* v_cont_3030_, lean_object* v_a_3031_, lean_object* v_goal_3032_, lean_object* v_ctorName_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3028_, v_clears_3029_, v_cont_3030_, v_a_3031_, v_goal_3032_, v_ctorName_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_ctorName_3033_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___boxed(lean_object* v_g_3043_, lean_object* v_fs_3044_, lean_object* v_clears_3045_, lean_object* v_e_3046_, lean_object* v_a_3047_, lean_object* v_pat_3048_, lean_object* v_cont_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3043_, v_fs_3044_, v_clears_3045_, v_e_3046_, v_a_3047_, v_pat_3048_, v_cont_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec_ref(v_e_3046_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(lean_object* v_00_u03b1_3058_, lean_object* v_g_3059_, lean_object* v_fs_3060_, lean_object* v_clears_3061_, lean_object* v_a_3062_, lean_object* v_pats_3063_, lean_object* v_cont_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___redArg(v_g_3059_, v_fs_3060_, v_clears_3061_, v_a_3062_, v_pats_3063_, v_cont_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue___boxed(lean_object* v_00_u03b1_3073_, lean_object* v_g_3074_, lean_object* v_fs_3075_, lean_object* v_clears_3076_, lean_object* v_a_3077_, lean_object* v_pats_3078_, lean_object* v_cont_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesContinue(v_00_u03b1_3073_, v_g_3074_, v_fs_3075_, v_clears_3076_, v_a_3077_, v_pats_3078_, v_cont_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(lean_object* v_00_u03b1_3088_, lean_object* v_fs_3089_, lean_object* v_clears_3090_, lean_object* v_cont_3091_, lean_object* v_a_3092_, lean_object* v_goal_3093_, lean_object* v_ctorName_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___redArg(v_fs_3089_, v_clears_3090_, v_cont_3091_, v_a_3092_, v_goal_3093_, v_ctorName_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_fs_3105_, lean_object* v_clears_3106_, lean_object* v_cont_3107_, lean_object* v_a_3108_, lean_object* v_goal_3109_, lean_object* v_ctorName_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_align(v_00_u03b1_3104_, v_fs_3105_, v_clears_3106_, v_cont_3107_, v_a_3108_, v_goal_3109_, v_ctorName_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_ctorName_3110_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(lean_object* v_00_u03b1_3120_, lean_object* v_mvarId_3121_, lean_object* v_x_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_mvarId_3121_, v_x_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_mvarId_3132_, lean_object* v_x_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7(v_00_u03b1_3131_, v_mvarId_3132_, v_x_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(lean_object* v_00_u03b1_3142_, lean_object* v_g_3143_, lean_object* v_fs_3144_, lean_object* v_clears_3145_, lean_object* v_e_3146_, lean_object* v_a_3147_, lean_object* v_pat_3148_, lean_object* v_cont_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_g_3143_, v_fs_3144_, v_clears_3145_, v_e_3146_, v_a_3147_, v_pat_3148_, v_cont_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___boxed(lean_object* v_00_u03b1_3158_, lean_object* v_g_3159_, lean_object* v_fs_3160_, lean_object* v_clears_3161_, lean_object* v_e_3162_, lean_object* v_a_3163_, lean_object* v_pat_3164_, lean_object* v_cont_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore(v_00_u03b1_3158_, v_g_3159_, v_fs_3160_, v_clears_3161_, v_e_3162_, v_a_3163_, v_pat_3164_, v_cont_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec_ref(v_e_3162_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(lean_object* v_00_u03b1_3174_, lean_object* v_fs_3175_, lean_object* v_clears_3176_, lean_object* v_cont_3177_, lean_object* v_as_3178_, size_t v_i_3179_, size_t v_stop_3180_, lean_object* v_b_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___redArg(v_fs_3175_, v_clears_3176_, v_cont_3177_, v_as_3178_, v_i_3179_, v_stop_3180_, v_b_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3___boxed(lean_object* v_00_u03b1_3190_, lean_object* v_fs_3191_, lean_object* v_clears_3192_, lean_object* v_cont_3193_, lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_stop_3196_, lean_object* v_b_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
size_t v_i_boxed_3205_; size_t v_stop_boxed_3206_; lean_object* v_res_3207_; 
v_i_boxed_3205_ = lean_unbox_usize(v_i_3195_);
lean_dec(v_i_3195_);
v_stop_boxed_3206_ = lean_unbox_usize(v_stop_3196_);
lean_dec(v_stop_3196_);
v_res_3207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__3(v_00_u03b1_3190_, v_fs_3191_, v_clears_3192_, v_cont_3193_, v_as_3194_, v_i_boxed_3205_, v_stop_boxed_3206_, v_b_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec_ref(v_as_3194_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(lean_object* v_mvarId_3208_, lean_object* v_val_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___redArg(v_mvarId_3208_, v_val_3209_, v___y_3213_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5___boxed(lean_object* v_mvarId_3218_, lean_object* v_val_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5(v_mvarId_3218_, v_val_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(lean_object* v_00_u03b1_3228_, lean_object* v_msg_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___redArg(v_msg_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8(v_00_u03b1_3238_, v_msg_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5(lean_object* v_00_u03b2_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5___redArg(v_x_3249_, v_x_3250_, v_x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(lean_object* v_msgData_3253_, lean_object* v_macroStack_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___redArg(v_msgData_3253_, v_macroStack_3254_, v___y_3259_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9___boxed(lean_object* v_msgData_3263_, lean_object* v_macroStack_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__8_spec__9(v_msgData_3263_, v_macroStack_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, size_t v_x_3275_, size_t v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___redArg(v_x_3274_, v_x_3275_, v_x_3276_, v_x_3277_, v_x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7___boxed(lean_object* v_00_u03b2_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
size_t v_x_20951__boxed_3286_; size_t v_x_20952__boxed_3287_; lean_object* v_res_3288_; 
v_x_20951__boxed_3286_ = lean_unbox_usize(v_x_3282_);
lean_dec(v_x_3282_);
v_x_20952__boxed_3287_ = lean_unbox_usize(v_x_3283_);
lean_dec(v_x_3283_);
v_res_3288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7(v_00_u03b2_3280_, v_x_3281_, v_x_20951__boxed_3286_, v_x_20952__boxed_3287_, v_x_3284_, v_x_3285_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_3289_, lean_object* v_n_3290_, lean_object* v_k_3291_, lean_object* v_v_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10___redArg(v_n_3290_, v_k_3291_, v_v_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_3294_, size_t v_depth_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_entries_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___redArg(v_depth_3295_, v_keys_3296_, v_vals_3297_, v_i_3299_, v_entries_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_depth_3303_, lean_object* v_keys_3304_, lean_object* v_vals_3305_, lean_object* v_heq_3306_, lean_object* v_i_3307_, lean_object* v_entries_3308_){
_start:
{
size_t v_depth_boxed_3309_; lean_object* v_res_3310_; 
v_depth_boxed_3309_ = lean_unbox_usize(v_depth_3303_);
lean_dec(v_depth_3303_);
v_res_3310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__11(v_00_u03b2_3302_, v_depth_boxed_3309_, v_keys_3304_, v_vals_3305_, v_heq_3306_, v_i_3307_, v_entries_3308_);
lean_dec_ref(v_vals_3305_);
lean_dec_ref(v_keys_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__5_spec__5_spec__7_spec__10_spec__13___redArg(v_x_3312_, v_x_3313_, v_x_3314_, v_x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(lean_object* v_a_3317_, lean_object* v_as_3318_, size_t v_i_3319_, size_t v_stop_3320_){
_start:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_usize_dec_eq(v_i_3319_, v_stop_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = lean_array_uget_borrowed(v_as_3318_, v_i_3319_);
v___x_3323_ = l_Lean_instBEqFVarId_beq(v_a_3317_, v___x_3322_);
if (v___x_3323_ == 0)
{
size_t v___x_3324_; size_t v___x_3325_; 
v___x_3324_ = ((size_t)1ULL);
v___x_3325_ = lean_usize_add(v_i_3319_, v___x_3324_);
v_i_3319_ = v___x_3325_;
goto _start;
}
else
{
return v___x_3323_;
}
}
else
{
uint8_t v___x_3327_; 
v___x_3327_ = 0;
return v___x_3327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0___boxed(lean_object* v_a_3328_, lean_object* v_as_3329_, lean_object* v_i_3330_, lean_object* v_stop_3331_){
_start:
{
size_t v_i_boxed_3332_; size_t v_stop_boxed_3333_; uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_i_boxed_3332_ = lean_unbox_usize(v_i_3330_);
lean_dec(v_i_3330_);
v_stop_boxed_3333_ = lean_unbox_usize(v_stop_3331_);
lean_dec(v_stop_3331_);
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3328_, v_as_3329_, v_i_boxed_3332_, v_stop_boxed_3333_);
lean_dec_ref(v_as_3329_);
lean_dec(v_a_3328_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(lean_object* v_as_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_array_get_size(v_as_3336_);
v___x_3340_ = lean_nat_dec_lt(v___x_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
return v___x_3340_;
}
else
{
if (v___x_3340_ == 0)
{
return v___x_3340_;
}
else
{
size_t v___x_3341_; size_t v___x_3342_; uint8_t v___x_3343_; 
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = lean_usize_of_nat(v___x_3339_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0_spec__0(v_a_3337_, v_as_3336_, v___x_3341_, v___x_3342_);
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0___boxed(lean_object* v_as_3344_, lean_object* v_a_3345_){
_start:
{
uint8_t v_res_3346_; lean_object* v_r_3347_; 
v_res_3346_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_as_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_as_3344_);
v_r_3347_ = lean_box(v_res_3346_);
return v_r_3347_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(lean_object* v_snd_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_3350_; 
v___x_3350_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__0(v_snd_3348_, v___y_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed(lean_object* v_snd_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_res_3353_; lean_object* v_r_3354_; 
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1(v_snd_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec(v_snd_3351_);
v_r_3354_ = lean_box(v_res_3353_);
return v_r_3354_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(lean_object* v_x_3355_){
_start:
{
uint8_t v___x_3356_; 
v___x_3356_ = 0;
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0___boxed(lean_object* v_x_3357_){
_start:
{
uint8_t v_res_3358_; lean_object* v_r_3359_; 
v_res_3358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__0(v_x_3357_);
lean_dec(v_x_3357_);
v_r_3359_ = lean_box(v_res_3358_);
return v_r_3359_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_unsigned_to_nat(16u);
v___x_3363_ = lean_mk_array(v___x_3362_, v___x_3361_);
return v___x_3363_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__1);
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3364_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_as_3367_, size_t v_sz_3368_, size_t v_i_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_){
_start:
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_usize_dec_lt(v_i_3369_, v_sz_3368_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_b_3370_);
return v___x_3374_;
}
else
{
lean_object* v_snd_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3506_; 
v_snd_3375_ = lean_ctor_get(v_b_3370_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_b_3370_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v_b_3370_, 0);
lean_dec(v_unused_3507_);
v___x_3377_ = v_b_3370_;
v_isShared_3378_ = v_isSharedCheck_3506_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_snd_3375_);
lean_dec(v_b_3370_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3506_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; lean_object* v_a_3381_; lean_object* v_a_3388_; 
v___x_3379_ = lean_box(0);
v_a_3388_ = lean_array_uget_borrowed(v_as_3367_, v_i_3369_);
if (lean_obj_tag(v_a_3388_) == 0)
{
v_a_3381_ = v_snd_3375_;
goto v___jp_3380_;
}
else
{
lean_object* v_val_3389_; uint8_t v_a_3391_; lean_object* v___f_3394_; lean_object* v___f_3395_; 
v_val_3389_ = lean_ctor_get(v_a_3388_, 0);
v___f_3394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3375_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3395_, 0, v_snd_3375_);
if (lean_obj_tag(v_val_3389_) == 0)
{
lean_object* v_type_3396_; lean_object* v___x_3397_; uint8_t v_fst_3399_; lean_object* v_mctx_3400_; lean_object* v___y_3416_; lean_object* v_mctx_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v_type_3396_ = lean_ctor_get(v_val_3389_, 3);
v___x_3397_ = lean_st_ref_get(v___y_3371_);
v_mctx_3421_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref_n(v_mctx_3421_, 2);
lean_dec(v___x_3397_);
v___x_3422_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v_mctx_3421_);
v___x_3424_ = l_Lean_Expr_hasFVar(v_type_3396_);
if (v___x_3424_ == 0)
{
uint8_t v___x_3425_; 
v___x_3425_ = l_Lean_Expr_hasMVar(v_type_3396_);
if (v___x_3425_ == 0)
{
lean_dec_ref_known(v___x_3423_, 2);
lean_dec_ref(v___f_3395_);
v_fst_3399_ = v___x_3425_;
v_mctx_3400_ = v_mctx_3421_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3426_; 
lean_dec_ref(v_mctx_3421_);
lean_inc_ref(v_type_3396_);
v___x_3426_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3396_, v___x_3423_);
v___y_3416_ = v___x_3426_;
goto v___jp_3415_;
}
}
else
{
lean_object* v___x_3427_; 
lean_dec_ref(v_mctx_3421_);
lean_inc_ref(v_type_3396_);
v___x_3427_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3396_, v___x_3423_);
v___y_3416_ = v___x_3427_;
goto v___jp_3415_;
}
v___jp_3398_:
{
lean_object* v___x_3401_; lean_object* v_cache_3402_; lean_object* v_zetaDeltaFVarIds_3403_; lean_object* v_postponed_3404_; lean_object* v_diag_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3413_; 
v___x_3401_ = lean_st_ref_take(v___y_3371_);
v_cache_3402_ = lean_ctor_get(v___x_3401_, 1);
v_zetaDeltaFVarIds_3403_ = lean_ctor_get(v___x_3401_, 2);
v_postponed_3404_ = lean_ctor_get(v___x_3401_, 3);
v_diag_3405_ = lean_ctor_get(v___x_3401_, 4);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3401_, 0);
lean_dec(v_unused_3414_);
v___x_3407_ = v___x_3401_;
v_isShared_3408_ = v_isSharedCheck_3413_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_diag_3405_);
lean_inc(v_postponed_3404_);
lean_inc(v_zetaDeltaFVarIds_3403_);
lean_inc(v_cache_3402_);
lean_dec(v___x_3401_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3413_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v_mctx_3400_);
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_mctx_3400_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_cache_3402_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_zetaDeltaFVarIds_3403_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_postponed_3404_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_diag_3405_);
v___x_3410_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_st_ref_put(v___y_3371_, v___x_3410_);
v_a_3391_ = v_fst_3399_;
goto v___jp_3390_;
}
}
}
v___jp_3415_:
{
lean_object* v_snd_3417_; lean_object* v_fst_3418_; lean_object* v_mctx_3419_; uint8_t v___x_3420_; 
v_snd_3417_ = lean_ctor_get(v___y_3416_, 1);
lean_inc(v_snd_3417_);
v_fst_3418_ = lean_ctor_get(v___y_3416_, 0);
lean_inc(v_fst_3418_);
lean_dec_ref(v___y_3416_);
v_mctx_3419_ = lean_ctor_get(v_snd_3417_, 1);
lean_inc_ref(v_mctx_3419_);
lean_dec(v_snd_3417_);
v___x_3420_ = lean_unbox(v_fst_3418_);
lean_dec(v_fst_3418_);
v_fst_3399_ = v___x_3420_;
v_mctx_3400_ = v_mctx_3419_;
goto v___jp_3398_;
}
}
else
{
uint8_t v_nondep_3428_; 
v_nondep_3428_ = lean_ctor_get_uint8(v_val_3389_, sizeof(void*)*5);
if (v_nondep_3428_ == 0)
{
lean_object* v_type_3429_; lean_object* v_value_3430_; lean_object* v___x_3431_; uint8_t v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___y_3451_; uint8_t v_fst_3456_; lean_object* v_snd_3457_; lean_object* v___y_3463_; lean_object* v_mctx_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v_type_3429_ = lean_ctor_get(v_val_3389_, 3);
v_value_3430_ = lean_ctor_get(v_val_3389_, 4);
v___x_3431_ = lean_st_ref_get(v___y_3371_);
v_mctx_3467_ = lean_ctor_get(v___x_3431_, 0);
lean_inc_ref(v_mctx_3467_);
lean_dec(v___x_3431_);
v___x_3468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v_mctx_3467_);
v___x_3470_ = l_Lean_Expr_hasFVar(v_type_3429_);
if (v___x_3470_ == 0)
{
uint8_t v___x_3471_; 
v___x_3471_ = l_Lean_Expr_hasMVar(v_type_3429_);
if (v___x_3471_ == 0)
{
v_fst_3456_ = v___x_3471_;
v_snd_3457_ = v___x_3469_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3472_; 
lean_inc_ref(v_type_3429_);
lean_inc_ref(v___f_3395_);
v___x_3472_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3429_, v___x_3469_);
v___y_3463_ = v___x_3472_;
goto v___jp_3462_;
}
}
else
{
lean_object* v___x_3473_; 
lean_inc_ref(v_type_3429_);
lean_inc_ref(v___f_3395_);
v___x_3473_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3429_, v___x_3469_);
v___y_3463_ = v___x_3473_;
goto v___jp_3462_;
}
v___jp_3432_:
{
lean_object* v_mctx_3435_; lean_object* v___x_3436_; lean_object* v_cache_3437_; lean_object* v_zetaDeltaFVarIds_3438_; lean_object* v_postponed_3439_; lean_object* v_diag_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3448_; 
v_mctx_3435_ = lean_ctor_get(v_snd_3434_, 1);
lean_inc_ref(v_mctx_3435_);
lean_dec_ref(v_snd_3434_);
v___x_3436_ = lean_st_ref_take(v___y_3371_);
v_cache_3437_ = lean_ctor_get(v___x_3436_, 1);
v_zetaDeltaFVarIds_3438_ = lean_ctor_get(v___x_3436_, 2);
v_postponed_3439_ = lean_ctor_get(v___x_3436_, 3);
v_diag_3440_ = lean_ctor_get(v___x_3436_, 4);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v___x_3436_, 0);
lean_dec(v_unused_3449_);
v___x_3442_ = v___x_3436_;
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_diag_3440_);
lean_inc(v_postponed_3439_);
lean_inc(v_zetaDeltaFVarIds_3438_);
lean_inc(v_cache_3437_);
lean_dec(v___x_3436_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3448_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v_mctx_3435_);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_mctx_3435_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_cache_3437_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_zetaDeltaFVarIds_3438_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_postponed_3439_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_diag_3440_);
v___x_3445_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_st_ref_put(v___y_3371_, v___x_3445_);
v_a_3391_ = v_fst_3433_;
goto v___jp_3390_;
}
}
}
v___jp_3450_:
{
lean_object* v_fst_3452_; lean_object* v_snd_3453_; uint8_t v___x_3454_; 
v_fst_3452_ = lean_ctor_get(v___y_3451_, 0);
lean_inc(v_fst_3452_);
v_snd_3453_ = lean_ctor_get(v___y_3451_, 1);
lean_inc(v_snd_3453_);
lean_dec_ref(v___y_3451_);
v___x_3454_ = lean_unbox(v_fst_3452_);
lean_dec(v_fst_3452_);
v_fst_3433_ = v___x_3454_;
v_snd_3434_ = v_snd_3453_;
goto v___jp_3432_;
}
v___jp_3455_:
{
if (v_fst_3456_ == 0)
{
uint8_t v___x_3458_; 
v___x_3458_ = l_Lean_Expr_hasFVar(v_value_3430_);
if (v___x_3458_ == 0)
{
uint8_t v___x_3459_; 
v___x_3459_ = l_Lean_Expr_hasMVar(v_value_3430_);
if (v___x_3459_ == 0)
{
lean_dec_ref(v___f_3395_);
v_fst_3433_ = v___x_3459_;
v_snd_3434_ = v_snd_3457_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3460_; 
lean_inc_ref(v_value_3430_);
v___x_3460_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_value_3430_, v_snd_3457_);
v___y_3451_ = v___x_3460_;
goto v___jp_3450_;
}
}
else
{
lean_object* v___x_3461_; 
lean_inc_ref(v_value_3430_);
v___x_3461_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_value_3430_, v_snd_3457_);
v___y_3451_ = v___x_3461_;
goto v___jp_3450_;
}
}
else
{
lean_dec_ref(v___f_3395_);
v_fst_3433_ = v_fst_3456_;
v_snd_3434_ = v_snd_3457_;
goto v___jp_3432_;
}
}
v___jp_3462_:
{
lean_object* v_fst_3464_; lean_object* v_snd_3465_; uint8_t v___x_3466_; 
v_fst_3464_ = lean_ctor_get(v___y_3463_, 0);
lean_inc(v_fst_3464_);
v_snd_3465_ = lean_ctor_get(v___y_3463_, 1);
lean_inc(v_snd_3465_);
lean_dec_ref(v___y_3463_);
v___x_3466_ = lean_unbox(v_fst_3464_);
lean_dec(v_fst_3464_);
v_fst_3456_ = v___x_3466_;
v_snd_3457_ = v_snd_3465_;
goto v___jp_3455_;
}
}
else
{
lean_object* v_type_3474_; lean_object* v___x_3475_; uint8_t v_fst_3477_; lean_object* v_mctx_3478_; lean_object* v___y_3494_; lean_object* v_mctx_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_type_3474_ = lean_ctor_get(v_val_3389_, 3);
v___x_3475_ = lean_st_ref_get(v___y_3371_);
v_mctx_3499_ = lean_ctor_get(v___x_3475_, 0);
lean_inc_ref_n(v_mctx_3499_, 2);
lean_dec(v___x_3475_);
v___x_3500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v_mctx_3499_);
v___x_3502_ = l_Lean_Expr_hasFVar(v_type_3474_);
if (v___x_3502_ == 0)
{
uint8_t v___x_3503_; 
v___x_3503_ = l_Lean_Expr_hasMVar(v_type_3474_);
if (v___x_3503_ == 0)
{
lean_dec_ref_known(v___x_3501_, 2);
lean_dec_ref(v___f_3395_);
v_fst_3477_ = v___x_3503_;
v_mctx_3478_ = v_mctx_3499_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3504_; 
lean_dec_ref(v_mctx_3499_);
lean_inc_ref(v_type_3474_);
v___x_3504_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3474_, v___x_3501_);
v___y_3494_ = v___x_3504_;
goto v___jp_3493_;
}
}
else
{
lean_object* v___x_3505_; 
lean_dec_ref(v_mctx_3499_);
lean_inc_ref(v_type_3474_);
v___x_3505_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3395_, v___f_3394_, v_type_3474_, v___x_3501_);
v___y_3494_ = v___x_3505_;
goto v___jp_3493_;
}
v___jp_3476_:
{
lean_object* v___x_3479_; lean_object* v_cache_3480_; lean_object* v_zetaDeltaFVarIds_3481_; lean_object* v_postponed_3482_; lean_object* v_diag_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3491_; 
v___x_3479_ = lean_st_ref_take(v___y_3371_);
v_cache_3480_ = lean_ctor_get(v___x_3479_, 1);
v_zetaDeltaFVarIds_3481_ = lean_ctor_get(v___x_3479_, 2);
v_postponed_3482_ = lean_ctor_get(v___x_3479_, 3);
v_diag_3483_ = lean_ctor_get(v___x_3479_, 4);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3492_);
v___x_3485_ = v___x_3479_;
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_diag_3483_);
lean_inc(v_postponed_3482_);
lean_inc(v_zetaDeltaFVarIds_3481_);
lean_inc(v_cache_3480_);
lean_dec(v___x_3479_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v_mctx_3478_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_mctx_3478_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_cache_3480_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_zetaDeltaFVarIds_3481_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_postponed_3482_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_diag_3483_);
v___x_3488_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_st_ref_put(v___y_3371_, v___x_3488_);
v_a_3391_ = v_fst_3477_;
goto v___jp_3390_;
}
}
}
v___jp_3493_:
{
lean_object* v_snd_3495_; lean_object* v_fst_3496_; lean_object* v_mctx_3497_; uint8_t v___x_3498_; 
v_snd_3495_ = lean_ctor_get(v___y_3494_, 1);
lean_inc(v_snd_3495_);
v_fst_3496_ = lean_ctor_get(v___y_3494_, 0);
lean_inc(v_fst_3496_);
lean_dec_ref(v___y_3494_);
v_mctx_3497_ = lean_ctor_get(v_snd_3495_, 1);
lean_inc_ref(v_mctx_3497_);
lean_dec(v_snd_3495_);
v___x_3498_ = lean_unbox(v_fst_3496_);
lean_dec(v_fst_3496_);
v_fst_3477_ = v___x_3498_;
v_mctx_3478_ = v_mctx_3497_;
goto v___jp_3476_;
}
}
}
v___jp_3390_:
{
if (v_a_3391_ == 0)
{
v_a_3381_ = v_snd_3375_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = l_Lean_LocalDecl_fvarId(v_val_3389_);
v___x_3393_ = lean_array_push(v_snd_3375_, v___x_3392_);
v_a_3381_ = v___x_3393_;
goto v___jp_3380_;
}
}
}
v___jp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v_a_3381_);
lean_ctor_set(v___x_3377_, 0, v___x_3379_);
v___x_3383_ = v___x_3377_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_a_3381_);
v___x_3383_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
size_t v___x_3384_; size_t v___x_3385_; 
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_add(v_i_3369_, v___x_3384_);
v_i_3369_ = v___x_3385_;
v_b_3370_ = v___x_3383_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_as_3508_, lean_object* v_sz_3509_, lean_object* v_i_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
size_t v_sz_boxed_3514_; size_t v_i_boxed_3515_; lean_object* v_res_3516_; 
v_sz_boxed_3514_ = lean_unbox_usize(v_sz_3509_);
lean_dec(v_sz_3509_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3510_);
lean_dec(v_i_3510_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3508_, v_sz_boxed_3514_, v_i_boxed_3515_, v_b_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v_as_3508_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(lean_object* v_as_3517_, size_t v_sz_3518_, size_t v_i_3519_, lean_object* v_b_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_usize_dec_lt(v_i_3519_, v_sz_3518_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v_b_3520_);
return v___x_3527_;
}
else
{
lean_object* v_snd_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3659_; 
v_snd_3528_ = lean_ctor_get(v_b_3520_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_b_3520_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_b_3520_, 0);
lean_dec(v_unused_3660_);
v___x_3530_ = v_b_3520_;
v_isShared_3531_ = v_isSharedCheck_3659_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_snd_3528_);
lean_dec(v_b_3520_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3659_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v_a_3534_; lean_object* v_a_3541_; 
v___x_3532_ = lean_box(0);
v_a_3541_ = lean_array_uget_borrowed(v_as_3517_, v_i_3519_);
if (lean_obj_tag(v_a_3541_) == 0)
{
v_a_3534_ = v_snd_3528_;
goto v___jp_3533_;
}
else
{
lean_object* v_val_3542_; uint8_t v_a_3544_; lean_object* v___f_3547_; lean_object* v___f_3548_; 
v_val_3542_ = lean_ctor_get(v_a_3541_, 0);
v___f_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3528_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3548_, 0, v_snd_3528_);
if (lean_obj_tag(v_val_3542_) == 0)
{
lean_object* v_type_3549_; lean_object* v___x_3550_; uint8_t v_fst_3552_; lean_object* v_mctx_3553_; lean_object* v___y_3569_; lean_object* v_mctx_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_type_3549_ = lean_ctor_get(v_val_3542_, 3);
v___x_3550_ = lean_st_ref_get(v___y_3522_);
v_mctx_3574_ = lean_ctor_get(v___x_3550_, 0);
lean_inc_ref_n(v_mctx_3574_, 2);
lean_dec(v___x_3550_);
v___x_3575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v_mctx_3574_);
v___x_3577_ = l_Lean_Expr_hasFVar(v_type_3549_);
if (v___x_3577_ == 0)
{
uint8_t v___x_3578_; 
v___x_3578_ = l_Lean_Expr_hasMVar(v_type_3549_);
if (v___x_3578_ == 0)
{
lean_dec_ref_known(v___x_3576_, 2);
lean_dec_ref(v___f_3548_);
v_fst_3552_ = v___x_3578_;
v_mctx_3553_ = v_mctx_3574_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3579_; 
lean_dec_ref(v_mctx_3574_);
lean_inc_ref(v_type_3549_);
v___x_3579_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3549_, v___x_3576_);
v___y_3569_ = v___x_3579_;
goto v___jp_3568_;
}
}
else
{
lean_object* v___x_3580_; 
lean_dec_ref(v_mctx_3574_);
lean_inc_ref(v_type_3549_);
v___x_3580_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3549_, v___x_3576_);
v___y_3569_ = v___x_3580_;
goto v___jp_3568_;
}
v___jp_3551_:
{
lean_object* v___x_3554_; lean_object* v_cache_3555_; lean_object* v_zetaDeltaFVarIds_3556_; lean_object* v_postponed_3557_; lean_object* v_diag_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3566_; 
v___x_3554_ = lean_st_ref_take(v___y_3522_);
v_cache_3555_ = lean_ctor_get(v___x_3554_, 1);
v_zetaDeltaFVarIds_3556_ = lean_ctor_get(v___x_3554_, 2);
v_postponed_3557_ = lean_ctor_get(v___x_3554_, 3);
v_diag_3558_ = lean_ctor_get(v___x_3554_, 4);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3554_, 0);
lean_dec(v_unused_3567_);
v___x_3560_ = v___x_3554_;
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_diag_3558_);
lean_inc(v_postponed_3557_);
lean_inc(v_zetaDeltaFVarIds_3556_);
lean_inc(v_cache_3555_);
lean_dec(v___x_3554_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_mctx_3553_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_mctx_3553_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_cache_3555_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_zetaDeltaFVarIds_3556_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_postponed_3557_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_diag_3558_);
v___x_3563_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_st_ref_put(v___y_3522_, v___x_3563_);
v_a_3544_ = v_fst_3552_;
goto v___jp_3543_;
}
}
}
v___jp_3568_:
{
lean_object* v_snd_3570_; lean_object* v_fst_3571_; lean_object* v_mctx_3572_; uint8_t v___x_3573_; 
v_snd_3570_ = lean_ctor_get(v___y_3569_, 1);
lean_inc(v_snd_3570_);
v_fst_3571_ = lean_ctor_get(v___y_3569_, 0);
lean_inc(v_fst_3571_);
lean_dec_ref(v___y_3569_);
v_mctx_3572_ = lean_ctor_get(v_snd_3570_, 1);
lean_inc_ref(v_mctx_3572_);
lean_dec(v_snd_3570_);
v___x_3573_ = lean_unbox(v_fst_3571_);
lean_dec(v_fst_3571_);
v_fst_3552_ = v___x_3573_;
v_mctx_3553_ = v_mctx_3572_;
goto v___jp_3551_;
}
}
else
{
uint8_t v_nondep_3581_; 
v_nondep_3581_ = lean_ctor_get_uint8(v_val_3542_, sizeof(void*)*5);
if (v_nondep_3581_ == 0)
{
lean_object* v_type_3582_; lean_object* v_value_3583_; lean_object* v___x_3584_; uint8_t v_fst_3586_; lean_object* v_snd_3587_; lean_object* v___y_3604_; uint8_t v_fst_3609_; lean_object* v_snd_3610_; lean_object* v___y_3616_; lean_object* v_mctx_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; 
v_type_3582_ = lean_ctor_get(v_val_3542_, 3);
v_value_3583_ = lean_ctor_get(v_val_3542_, 4);
v___x_3584_ = lean_st_ref_get(v___y_3522_);
v_mctx_3620_ = lean_ctor_get(v___x_3584_, 0);
lean_inc_ref(v_mctx_3620_);
lean_dec(v___x_3584_);
v___x_3621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v_mctx_3620_);
v___x_3623_ = l_Lean_Expr_hasFVar(v_type_3582_);
if (v___x_3623_ == 0)
{
uint8_t v___x_3624_; 
v___x_3624_ = l_Lean_Expr_hasMVar(v_type_3582_);
if (v___x_3624_ == 0)
{
v_fst_3609_ = v___x_3624_;
v_snd_3610_ = v___x_3622_;
goto v___jp_3608_;
}
else
{
lean_object* v___x_3625_; 
lean_inc_ref(v_type_3582_);
lean_inc_ref(v___f_3548_);
v___x_3625_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3582_, v___x_3622_);
v___y_3616_ = v___x_3625_;
goto v___jp_3615_;
}
}
else
{
lean_object* v___x_3626_; 
lean_inc_ref(v_type_3582_);
lean_inc_ref(v___f_3548_);
v___x_3626_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3582_, v___x_3622_);
v___y_3616_ = v___x_3626_;
goto v___jp_3615_;
}
v___jp_3585_:
{
lean_object* v_mctx_3588_; lean_object* v___x_3589_; lean_object* v_cache_3590_; lean_object* v_zetaDeltaFVarIds_3591_; lean_object* v_postponed_3592_; lean_object* v_diag_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3601_; 
v_mctx_3588_ = lean_ctor_get(v_snd_3587_, 1);
lean_inc_ref(v_mctx_3588_);
lean_dec_ref(v_snd_3587_);
v___x_3589_ = lean_st_ref_take(v___y_3522_);
v_cache_3590_ = lean_ctor_get(v___x_3589_, 1);
v_zetaDeltaFVarIds_3591_ = lean_ctor_get(v___x_3589_, 2);
v_postponed_3592_ = lean_ctor_get(v___x_3589_, 3);
v_diag_3593_ = lean_ctor_get(v___x_3589_, 4);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; 
v_unused_3602_ = lean_ctor_get(v___x_3589_, 0);
lean_dec(v_unused_3602_);
v___x_3595_ = v___x_3589_;
v_isShared_3596_ = v_isSharedCheck_3601_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_diag_3593_);
lean_inc(v_postponed_3592_);
lean_inc(v_zetaDeltaFVarIds_3591_);
lean_inc(v_cache_3590_);
lean_dec(v___x_3589_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3601_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v_mctx_3588_);
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_mctx_3588_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_cache_3590_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_zetaDeltaFVarIds_3591_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_postponed_3592_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_diag_3593_);
v___x_3598_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_st_ref_put(v___y_3522_, v___x_3598_);
v_a_3544_ = v_fst_3586_;
goto v___jp_3543_;
}
}
}
v___jp_3603_:
{
lean_object* v_fst_3605_; lean_object* v_snd_3606_; uint8_t v___x_3607_; 
v_fst_3605_ = lean_ctor_get(v___y_3604_, 0);
lean_inc(v_fst_3605_);
v_snd_3606_ = lean_ctor_get(v___y_3604_, 1);
lean_inc(v_snd_3606_);
lean_dec_ref(v___y_3604_);
v___x_3607_ = lean_unbox(v_fst_3605_);
lean_dec(v_fst_3605_);
v_fst_3586_ = v___x_3607_;
v_snd_3587_ = v_snd_3606_;
goto v___jp_3585_;
}
v___jp_3608_:
{
if (v_fst_3609_ == 0)
{
uint8_t v___x_3611_; 
v___x_3611_ = l_Lean_Expr_hasFVar(v_value_3583_);
if (v___x_3611_ == 0)
{
uint8_t v___x_3612_; 
v___x_3612_ = l_Lean_Expr_hasMVar(v_value_3583_);
if (v___x_3612_ == 0)
{
lean_dec_ref(v___f_3548_);
v_fst_3586_ = v___x_3612_;
v_snd_3587_ = v_snd_3610_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3613_; 
lean_inc_ref(v_value_3583_);
v___x_3613_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_value_3583_, v_snd_3610_);
v___y_3604_ = v___x_3613_;
goto v___jp_3603_;
}
}
else
{
lean_object* v___x_3614_; 
lean_inc_ref(v_value_3583_);
v___x_3614_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_value_3583_, v_snd_3610_);
v___y_3604_ = v___x_3614_;
goto v___jp_3603_;
}
}
else
{
lean_dec_ref(v___f_3548_);
v_fst_3586_ = v_fst_3609_;
v_snd_3587_ = v_snd_3610_;
goto v___jp_3585_;
}
}
v___jp_3615_:
{
lean_object* v_fst_3617_; lean_object* v_snd_3618_; uint8_t v___x_3619_; 
v_fst_3617_ = lean_ctor_get(v___y_3616_, 0);
lean_inc(v_fst_3617_);
v_snd_3618_ = lean_ctor_get(v___y_3616_, 1);
lean_inc(v_snd_3618_);
lean_dec_ref(v___y_3616_);
v___x_3619_ = lean_unbox(v_fst_3617_);
lean_dec(v_fst_3617_);
v_fst_3609_ = v___x_3619_;
v_snd_3610_ = v_snd_3618_;
goto v___jp_3608_;
}
}
else
{
lean_object* v_type_3627_; lean_object* v___x_3628_; uint8_t v_fst_3630_; lean_object* v_mctx_3631_; lean_object* v___y_3647_; lean_object* v_mctx_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v_type_3627_ = lean_ctor_get(v_val_3542_, 3);
v___x_3628_ = lean_st_ref_get(v___y_3522_);
v_mctx_3652_ = lean_ctor_get(v___x_3628_, 0);
lean_inc_ref_n(v_mctx_3652_, 2);
lean_dec(v___x_3628_);
v___x_3653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_mctx_3652_);
v___x_3655_ = l_Lean_Expr_hasFVar(v_type_3627_);
if (v___x_3655_ == 0)
{
uint8_t v___x_3656_; 
v___x_3656_ = l_Lean_Expr_hasMVar(v_type_3627_);
if (v___x_3656_ == 0)
{
lean_dec_ref_known(v___x_3654_, 2);
lean_dec_ref(v___f_3548_);
v_fst_3630_ = v___x_3656_;
v_mctx_3631_ = v_mctx_3652_;
goto v___jp_3629_;
}
else
{
lean_object* v___x_3657_; 
lean_dec_ref(v_mctx_3652_);
lean_inc_ref(v_type_3627_);
v___x_3657_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3627_, v___x_3654_);
v___y_3647_ = v___x_3657_;
goto v___jp_3646_;
}
}
else
{
lean_object* v___x_3658_; 
lean_dec_ref(v_mctx_3652_);
lean_inc_ref(v_type_3627_);
v___x_3658_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3548_, v___f_3547_, v_type_3627_, v___x_3654_);
v___y_3647_ = v___x_3658_;
goto v___jp_3646_;
}
v___jp_3629_:
{
lean_object* v___x_3632_; lean_object* v_cache_3633_; lean_object* v_zetaDeltaFVarIds_3634_; lean_object* v_postponed_3635_; lean_object* v_diag_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3644_; 
v___x_3632_ = lean_st_ref_take(v___y_3522_);
v_cache_3633_ = lean_ctor_get(v___x_3632_, 1);
v_zetaDeltaFVarIds_3634_ = lean_ctor_get(v___x_3632_, 2);
v_postponed_3635_ = lean_ctor_get(v___x_3632_, 3);
v_diag_3636_ = lean_ctor_get(v___x_3632_, 4);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v___x_3632_, 0);
lean_dec(v_unused_3645_);
v___x_3638_ = v___x_3632_;
v_isShared_3639_ = v_isSharedCheck_3644_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_diag_3636_);
lean_inc(v_postponed_3635_);
lean_inc(v_zetaDeltaFVarIds_3634_);
lean_inc(v_cache_3633_);
lean_dec(v___x_3632_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3644_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_mctx_3631_);
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_mctx_3631_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_cache_3633_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_zetaDeltaFVarIds_3634_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_postponed_3635_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_diag_3636_);
v___x_3641_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_st_ref_put(v___y_3522_, v___x_3641_);
v_a_3544_ = v_fst_3630_;
goto v___jp_3543_;
}
}
}
v___jp_3646_:
{
lean_object* v_snd_3648_; lean_object* v_fst_3649_; lean_object* v_mctx_3650_; uint8_t v___x_3651_; 
v_snd_3648_ = lean_ctor_get(v___y_3647_, 1);
lean_inc(v_snd_3648_);
v_fst_3649_ = lean_ctor_get(v___y_3647_, 0);
lean_inc(v_fst_3649_);
lean_dec_ref(v___y_3647_);
v_mctx_3650_ = lean_ctor_get(v_snd_3648_, 1);
lean_inc_ref(v_mctx_3650_);
lean_dec(v_snd_3648_);
v___x_3651_ = lean_unbox(v_fst_3649_);
lean_dec(v_fst_3649_);
v_fst_3630_ = v___x_3651_;
v_mctx_3631_ = v_mctx_3650_;
goto v___jp_3629_;
}
}
}
v___jp_3543_:
{
if (v_a_3544_ == 0)
{
v_a_3534_ = v_snd_3528_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = l_Lean_LocalDecl_fvarId(v_val_3542_);
v___x_3546_ = lean_array_push(v_snd_3528_, v___x_3545_);
v_a_3534_ = v___x_3546_;
goto v___jp_3533_;
}
}
}
v___jp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v_a_3534_);
lean_ctor_set(v___x_3530_, 0, v___x_3532_);
v___x_3536_ = v___x_3530_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_a_3534_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
size_t v___x_3537_; size_t v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((size_t)1ULL);
v___x_3538_ = lean_usize_add(v_i_3519_, v___x_3537_);
v___x_3539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_3517_, v_sz_3518_, v___x_3538_, v___x_3536_, v___y_3522_);
return v___x_3539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4___boxed(lean_object* v_as_3661_, lean_object* v_sz_3662_, lean_object* v_i_3663_, lean_object* v_b_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
size_t v_sz_boxed_3670_; size_t v_i_boxed_3671_; lean_object* v_res_3672_; 
v_sz_boxed_3670_ = lean_unbox_usize(v_sz_3662_);
lean_dec(v_sz_3662_);
v_i_boxed_3671_ = lean_unbox_usize(v_i_3663_);
lean_dec(v_i_3663_);
v_res_3672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_as_3661_, v_sz_boxed_3670_, v_i_boxed_3671_, v_b_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec_ref(v_as_3661_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(lean_object* v_init_3673_, lean_object* v_n_3674_, lean_object* v_b_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
if (lean_obj_tag(v_n_3674_) == 0)
{
lean_object* v_cs_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; size_t v_sz_3684_; size_t v___x_3685_; lean_object* v___x_3686_; 
v_cs_3681_ = lean_ctor_get(v_n_3674_, 0);
v___x_3682_ = lean_box(0);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
lean_ctor_set(v___x_3683_, 1, v_b_3675_);
v_sz_3684_ = lean_array_size(v_cs_3681_);
v___x_3685_ = ((size_t)0ULL);
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3673_, v_cs_3681_, v_sz_3684_, v___x_3685_, v___x_3683_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3701_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3701_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3701_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_fst_3691_; 
v_fst_3691_ = lean_ctor_get(v_a_3687_, 0);
if (lean_obj_tag(v_fst_3691_) == 0)
{
lean_object* v_snd_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v_snd_3692_ = lean_ctor_get(v_a_3687_, 1);
lean_inc(v_snd_3692_);
lean_dec(v_a_3687_);
v___x_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_snd_3692_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3693_);
v___x_3695_ = v___x_3689_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
else
{
lean_object* v_val_3697_; lean_object* v___x_3699_; 
lean_inc_ref(v_fst_3691_);
lean_dec(v_a_3687_);
v_val_3697_ = lean_ctor_get(v_fst_3691_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v_fst_3691_, 1);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v_val_3697_);
v___x_3699_ = v___x_3689_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_val_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_a_3702_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3686_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3686_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
else
{
lean_object* v_vs_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; size_t v_sz_3713_; size_t v___x_3714_; lean_object* v___x_3715_; 
v_vs_3710_ = lean_ctor_get(v_n_3674_, 0);
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v_b_3675_);
v_sz_3713_ = lean_array_size(v_vs_3710_);
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4(v_vs_3710_, v_sz_3713_, v___x_3714_, v___x_3712_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3730_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v_fst_3720_; 
v_fst_3720_ = lean_ctor_get(v_a_3716_, 0);
if (lean_obj_tag(v_fst_3720_) == 0)
{
lean_object* v_snd_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v_snd_3721_ = lean_ctor_get(v_a_3716_, 1);
lean_inc(v_snd_3721_);
lean_dec(v_a_3716_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v_snd_3721_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3722_);
v___x_3724_ = v___x_3718_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
else
{
lean_object* v_val_3726_; lean_object* v___x_3728_; 
lean_inc_ref(v_fst_3720_);
lean_dec(v_a_3716_);
v_val_3726_ = lean_ctor_get(v_fst_3720_, 0);
lean_inc(v_val_3726_);
lean_dec_ref_known(v_fst_3720_, 1);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v_val_3726_);
v___x_3728_ = v___x_3718_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_val_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3715_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3715_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(lean_object* v_init_3739_, lean_object* v_as_3740_, size_t v_sz_3741_, size_t v_i_3742_, lean_object* v_b_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_usize_dec_lt(v_i_3742_, v_sz_3741_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_b_3743_);
return v___x_3750_;
}
else
{
lean_object* v_snd_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3785_; 
v_snd_3751_ = lean_ctor_get(v_b_3743_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_b_3743_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; 
v_unused_3786_ = lean_ctor_get(v_b_3743_, 0);
lean_dec(v_unused_3786_);
v___x_3753_ = v_b_3743_;
v_isShared_3754_ = v_isSharedCheck_3785_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_snd_3751_);
lean_dec(v_b_3743_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3785_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_a_3755_; lean_object* v___x_3756_; 
v_a_3755_ = lean_array_uget_borrowed(v_as_3740_, v_i_3742_);
lean_inc(v_snd_3751_);
v___x_3756_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3739_, v_a_3755_, v_snd_3751_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3776_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3776_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3776_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
if (lean_obj_tag(v_a_3757_) == 0)
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3757_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3761_);
v___x_3763_ = v___x_3753_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_snd_3751_);
v___x_3763_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3765_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3763_);
v___x_3765_ = v___x_3759_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
lean_del_object(v___x_3759_);
lean_dec(v_snd_3751_);
v_a_3768_ = lean_ctor_get(v_a_3757_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v_a_3757_, 1);
v___x_3769_ = lean_box(0);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 1, v_a_3768_);
lean_ctor_set(v___x_3753_, 0, v___x_3769_);
v___x_3771_ = v___x_3753_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_a_3768_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
size_t v___x_3772_; size_t v___x_3773_; 
v___x_3772_ = ((size_t)1ULL);
v___x_3773_ = lean_usize_add(v_i_3742_, v___x_3772_);
v_i_3742_ = v___x_3773_;
v_b_3743_ = v___x_3771_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_del_object(v___x_3753_);
lean_dec(v_snd_3751_);
v_a_3777_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3756_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3756_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3___boxed(lean_object* v_init_3787_, lean_object* v_as_3788_, lean_object* v_sz_3789_, lean_object* v_i_3790_, lean_object* v_b_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3789_);
lean_dec(v_sz_3789_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3790_);
lean_dec(v_i_3790_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__3(v_init_3787_, v_as_3788_, v_sz_boxed_3797_, v_i_boxed_3798_, v_b_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec_ref(v_as_3788_);
lean_dec_ref(v_init_3787_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2___boxed(lean_object* v_init_3800_, lean_object* v_n_3801_, lean_object* v_b_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_3800_, v_n_3801_, v_b_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v_n_3801_);
lean_dec_ref(v_init_3800_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(lean_object* v_as_3809_, size_t v_sz_3810_, size_t v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v___x_3815_; 
v___x_3815_ = lean_usize_dec_lt(v_i_3811_, v_sz_3810_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_b_3812_);
return v___x_3816_;
}
else
{
lean_object* v_snd_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3948_; 
v_snd_3817_ = lean_ctor_get(v_b_3812_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_b_3812_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; 
v_unused_3949_ = lean_ctor_get(v_b_3812_, 0);
lean_dec(v_unused_3949_);
v___x_3819_ = v_b_3812_;
v_isShared_3820_ = v_isSharedCheck_3948_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_snd_3817_);
lean_dec(v_b_3812_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3948_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v_a_3823_; lean_object* v_a_3830_; 
v___x_3821_ = lean_box(0);
v_a_3830_ = lean_array_uget_borrowed(v_as_3809_, v_i_3811_);
if (lean_obj_tag(v_a_3830_) == 0)
{
v_a_3823_ = v_snd_3817_;
goto v___jp_3822_;
}
else
{
lean_object* v_val_3831_; uint8_t v_a_3833_; lean_object* v___f_3836_; lean_object* v___f_3837_; 
v_val_3831_ = lean_ctor_get(v_a_3830_, 0);
v___f_3836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3817_);
v___f_3837_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3837_, 0, v_snd_3817_);
if (lean_obj_tag(v_val_3831_) == 0)
{
lean_object* v_type_3838_; lean_object* v___x_3839_; uint8_t v_fst_3841_; lean_object* v_mctx_3842_; lean_object* v___y_3858_; lean_object* v_mctx_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_type_3838_ = lean_ctor_get(v_val_3831_, 3);
v___x_3839_ = lean_st_ref_get(v___y_3813_);
v_mctx_3863_ = lean_ctor_get(v___x_3839_, 0);
lean_inc_ref_n(v_mctx_3863_, 2);
lean_dec(v___x_3839_);
v___x_3864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v_mctx_3863_);
v___x_3866_ = l_Lean_Expr_hasFVar(v_type_3838_);
if (v___x_3866_ == 0)
{
uint8_t v___x_3867_; 
v___x_3867_ = l_Lean_Expr_hasMVar(v_type_3838_);
if (v___x_3867_ == 0)
{
lean_dec_ref_known(v___x_3865_, 2);
lean_dec_ref(v___f_3837_);
v_fst_3841_ = v___x_3867_;
v_mctx_3842_ = v_mctx_3863_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_mctx_3863_);
lean_inc_ref(v_type_3838_);
v___x_3868_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3838_, v___x_3865_);
v___y_3858_ = v___x_3868_;
goto v___jp_3857_;
}
}
else
{
lean_object* v___x_3869_; 
lean_dec_ref(v_mctx_3863_);
lean_inc_ref(v_type_3838_);
v___x_3869_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3838_, v___x_3865_);
v___y_3858_ = v___x_3869_;
goto v___jp_3857_;
}
v___jp_3840_:
{
lean_object* v___x_3843_; lean_object* v_cache_3844_; lean_object* v_zetaDeltaFVarIds_3845_; lean_object* v_postponed_3846_; lean_object* v_diag_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3855_; 
v___x_3843_ = lean_st_ref_take(v___y_3813_);
v_cache_3844_ = lean_ctor_get(v___x_3843_, 1);
v_zetaDeltaFVarIds_3845_ = lean_ctor_get(v___x_3843_, 2);
v_postponed_3846_ = lean_ctor_get(v___x_3843_, 3);
v_diag_3847_ = lean_ctor_get(v___x_3843_, 4);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v___x_3843_, 0);
lean_dec(v_unused_3856_);
v___x_3849_ = v___x_3843_;
v_isShared_3850_ = v_isSharedCheck_3855_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_diag_3847_);
lean_inc(v_postponed_3846_);
lean_inc(v_zetaDeltaFVarIds_3845_);
lean_inc(v_cache_3844_);
lean_dec(v___x_3843_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3855_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v_mctx_3842_);
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_mctx_3842_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_cache_3844_);
lean_ctor_set(v_reuseFailAlloc_3854_, 2, v_zetaDeltaFVarIds_3845_);
lean_ctor_set(v_reuseFailAlloc_3854_, 3, v_postponed_3846_);
lean_ctor_set(v_reuseFailAlloc_3854_, 4, v_diag_3847_);
v___x_3852_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_st_ref_put(v___y_3813_, v___x_3852_);
v_a_3833_ = v_fst_3841_;
goto v___jp_3832_;
}
}
}
v___jp_3857_:
{
lean_object* v_snd_3859_; lean_object* v_fst_3860_; lean_object* v_mctx_3861_; uint8_t v___x_3862_; 
v_snd_3859_ = lean_ctor_get(v___y_3858_, 1);
lean_inc(v_snd_3859_);
v_fst_3860_ = lean_ctor_get(v___y_3858_, 0);
lean_inc(v_fst_3860_);
lean_dec_ref(v___y_3858_);
v_mctx_3861_ = lean_ctor_get(v_snd_3859_, 1);
lean_inc_ref(v_mctx_3861_);
lean_dec(v_snd_3859_);
v___x_3862_ = lean_unbox(v_fst_3860_);
lean_dec(v_fst_3860_);
v_fst_3841_ = v___x_3862_;
v_mctx_3842_ = v_mctx_3861_;
goto v___jp_3840_;
}
}
else
{
uint8_t v_nondep_3870_; 
v_nondep_3870_ = lean_ctor_get_uint8(v_val_3831_, sizeof(void*)*5);
if (v_nondep_3870_ == 0)
{
lean_object* v_type_3871_; lean_object* v_value_3872_; lean_object* v___x_3873_; uint8_t v_fst_3875_; lean_object* v_snd_3876_; lean_object* v___y_3893_; uint8_t v_fst_3898_; lean_object* v_snd_3899_; lean_object* v___y_3905_; lean_object* v_mctx_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v_type_3871_ = lean_ctor_get(v_val_3831_, 3);
v_value_3872_ = lean_ctor_get(v_val_3831_, 4);
v___x_3873_ = lean_st_ref_get(v___y_3813_);
v_mctx_3909_ = lean_ctor_get(v___x_3873_, 0);
lean_inc_ref(v_mctx_3909_);
lean_dec(v___x_3873_);
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
lean_ctor_set(v___x_3911_, 1, v_mctx_3909_);
v___x_3912_ = l_Lean_Expr_hasFVar(v_type_3871_);
if (v___x_3912_ == 0)
{
uint8_t v___x_3913_; 
v___x_3913_ = l_Lean_Expr_hasMVar(v_type_3871_);
if (v___x_3913_ == 0)
{
v_fst_3898_ = v___x_3913_;
v_snd_3899_ = v___x_3911_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3914_; 
lean_inc_ref(v_type_3871_);
lean_inc_ref(v___f_3837_);
v___x_3914_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3871_, v___x_3911_);
v___y_3905_ = v___x_3914_;
goto v___jp_3904_;
}
}
else
{
lean_object* v___x_3915_; 
lean_inc_ref(v_type_3871_);
lean_inc_ref(v___f_3837_);
v___x_3915_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3871_, v___x_3911_);
v___y_3905_ = v___x_3915_;
goto v___jp_3904_;
}
v___jp_3874_:
{
lean_object* v_mctx_3877_; lean_object* v___x_3878_; lean_object* v_cache_3879_; lean_object* v_zetaDeltaFVarIds_3880_; lean_object* v_postponed_3881_; lean_object* v_diag_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_mctx_3877_ = lean_ctor_get(v_snd_3876_, 1);
lean_inc_ref(v_mctx_3877_);
lean_dec_ref(v_snd_3876_);
v___x_3878_ = lean_st_ref_take(v___y_3813_);
v_cache_3879_ = lean_ctor_get(v___x_3878_, 1);
v_zetaDeltaFVarIds_3880_ = lean_ctor_get(v___x_3878_, 2);
v_postponed_3881_ = lean_ctor_get(v___x_3878_, 3);
v_diag_3882_ = lean_ctor_get(v___x_3878_, 4);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3878_, 0);
lean_dec(v_unused_3891_);
v___x_3884_ = v___x_3878_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_diag_3882_);
lean_inc(v_postponed_3881_);
lean_inc(v_zetaDeltaFVarIds_3880_);
lean_inc(v_cache_3879_);
lean_dec(v___x_3878_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v_mctx_3877_);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_mctx_3877_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_cache_3879_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_zetaDeltaFVarIds_3880_);
lean_ctor_set(v_reuseFailAlloc_3889_, 3, v_postponed_3881_);
lean_ctor_set(v_reuseFailAlloc_3889_, 4, v_diag_3882_);
v___x_3887_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_st_ref_put(v___y_3813_, v___x_3887_);
v_a_3833_ = v_fst_3875_;
goto v___jp_3832_;
}
}
}
v___jp_3892_:
{
lean_object* v_fst_3894_; lean_object* v_snd_3895_; uint8_t v___x_3896_; 
v_fst_3894_ = lean_ctor_get(v___y_3893_, 0);
lean_inc(v_fst_3894_);
v_snd_3895_ = lean_ctor_get(v___y_3893_, 1);
lean_inc(v_snd_3895_);
lean_dec_ref(v___y_3893_);
v___x_3896_ = lean_unbox(v_fst_3894_);
lean_dec(v_fst_3894_);
v_fst_3875_ = v___x_3896_;
v_snd_3876_ = v_snd_3895_;
goto v___jp_3874_;
}
v___jp_3897_:
{
if (v_fst_3898_ == 0)
{
uint8_t v___x_3900_; 
v___x_3900_ = l_Lean_Expr_hasFVar(v_value_3872_);
if (v___x_3900_ == 0)
{
uint8_t v___x_3901_; 
v___x_3901_ = l_Lean_Expr_hasMVar(v_value_3872_);
if (v___x_3901_ == 0)
{
lean_dec_ref(v___f_3837_);
v_fst_3875_ = v___x_3901_;
v_snd_3876_ = v_snd_3899_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3902_; 
lean_inc_ref(v_value_3872_);
v___x_3902_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_value_3872_, v_snd_3899_);
v___y_3893_ = v___x_3902_;
goto v___jp_3892_;
}
}
else
{
lean_object* v___x_3903_; 
lean_inc_ref(v_value_3872_);
v___x_3903_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_value_3872_, v_snd_3899_);
v___y_3893_ = v___x_3903_;
goto v___jp_3892_;
}
}
else
{
lean_dec_ref(v___f_3837_);
v_fst_3875_ = v_fst_3898_;
v_snd_3876_ = v_snd_3899_;
goto v___jp_3874_;
}
}
v___jp_3904_:
{
lean_object* v_fst_3906_; lean_object* v_snd_3907_; uint8_t v___x_3908_; 
v_fst_3906_ = lean_ctor_get(v___y_3905_, 0);
lean_inc(v_fst_3906_);
v_snd_3907_ = lean_ctor_get(v___y_3905_, 1);
lean_inc(v_snd_3907_);
lean_dec_ref(v___y_3905_);
v___x_3908_ = lean_unbox(v_fst_3906_);
lean_dec(v_fst_3906_);
v_fst_3898_ = v___x_3908_;
v_snd_3899_ = v_snd_3907_;
goto v___jp_3897_;
}
}
else
{
lean_object* v_type_3916_; lean_object* v___x_3917_; uint8_t v_fst_3919_; lean_object* v_mctx_3920_; lean_object* v___y_3936_; lean_object* v_mctx_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v_type_3916_ = lean_ctor_get(v_val_3831_, 3);
v___x_3917_ = lean_st_ref_get(v___y_3813_);
v_mctx_3941_ = lean_ctor_get(v___x_3917_, 0);
lean_inc_ref_n(v_mctx_3941_, 2);
lean_dec(v___x_3917_);
v___x_3942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v_mctx_3941_);
v___x_3944_ = l_Lean_Expr_hasFVar(v_type_3916_);
if (v___x_3944_ == 0)
{
uint8_t v___x_3945_; 
v___x_3945_ = l_Lean_Expr_hasMVar(v_type_3916_);
if (v___x_3945_ == 0)
{
lean_dec_ref_known(v___x_3943_, 2);
lean_dec_ref(v___f_3837_);
v_fst_3919_ = v___x_3945_;
v_mctx_3920_ = v_mctx_3941_;
goto v___jp_3918_;
}
else
{
lean_object* v___x_3946_; 
lean_dec_ref(v_mctx_3941_);
lean_inc_ref(v_type_3916_);
v___x_3946_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3916_, v___x_3943_);
v___y_3936_ = v___x_3946_;
goto v___jp_3935_;
}
}
else
{
lean_object* v___x_3947_; 
lean_dec_ref(v_mctx_3941_);
lean_inc_ref(v_type_3916_);
v___x_3947_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3837_, v___f_3836_, v_type_3916_, v___x_3943_);
v___y_3936_ = v___x_3947_;
goto v___jp_3935_;
}
v___jp_3918_:
{
lean_object* v___x_3921_; lean_object* v_cache_3922_; lean_object* v_zetaDeltaFVarIds_3923_; lean_object* v_postponed_3924_; lean_object* v_diag_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3933_; 
v___x_3921_ = lean_st_ref_take(v___y_3813_);
v_cache_3922_ = lean_ctor_get(v___x_3921_, 1);
v_zetaDeltaFVarIds_3923_ = lean_ctor_get(v___x_3921_, 2);
v_postponed_3924_ = lean_ctor_get(v___x_3921_, 3);
v_diag_3925_ = lean_ctor_get(v___x_3921_, 4);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v___x_3921_, 0);
lean_dec(v_unused_3934_);
v___x_3927_ = v___x_3921_;
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_diag_3925_);
lean_inc(v_postponed_3924_);
lean_inc(v_zetaDeltaFVarIds_3923_);
lean_inc(v_cache_3922_);
lean_dec(v___x_3921_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v_mctx_3920_);
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_mctx_3920_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_cache_3922_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_zetaDeltaFVarIds_3923_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_postponed_3924_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_diag_3925_);
v___x_3930_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; 
v___x_3931_ = lean_st_ref_put(v___y_3813_, v___x_3930_);
v_a_3833_ = v_fst_3919_;
goto v___jp_3832_;
}
}
}
v___jp_3935_:
{
lean_object* v_snd_3937_; lean_object* v_fst_3938_; lean_object* v_mctx_3939_; uint8_t v___x_3940_; 
v_snd_3937_ = lean_ctor_get(v___y_3936_, 1);
lean_inc(v_snd_3937_);
v_fst_3938_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_fst_3938_);
lean_dec_ref(v___y_3936_);
v_mctx_3939_ = lean_ctor_get(v_snd_3937_, 1);
lean_inc_ref(v_mctx_3939_);
lean_dec(v_snd_3937_);
v___x_3940_ = lean_unbox(v_fst_3938_);
lean_dec(v_fst_3938_);
v_fst_3919_ = v___x_3940_;
v_mctx_3920_ = v_mctx_3939_;
goto v___jp_3918_;
}
}
}
v___jp_3832_:
{
if (v_a_3833_ == 0)
{
v_a_3823_ = v_snd_3817_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = l_Lean_LocalDecl_fvarId(v_val_3831_);
v___x_3835_ = lean_array_push(v_snd_3817_, v___x_3834_);
v_a_3823_ = v___x_3835_;
goto v___jp_3822_;
}
}
}
v___jp_3822_:
{
lean_object* v___x_3825_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 1, v_a_3823_);
lean_ctor_set(v___x_3819_, 0, v___x_3821_);
v___x_3825_ = v___x_3819_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_a_3823_);
v___x_3825_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
size_t v___x_3826_; size_t v___x_3827_; 
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = lean_usize_add(v_i_3811_, v___x_3826_);
v_i_3811_ = v___x_3827_;
v_b_3812_ = v___x_3825_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_3950_, lean_object* v_sz_3951_, lean_object* v_i_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
size_t v_sz_boxed_3956_; size_t v_i_boxed_3957_; lean_object* v_res_3958_; 
v_sz_boxed_3956_ = lean_unbox_usize(v_sz_3951_);
lean_dec(v_sz_3951_);
v_i_boxed_3957_ = lean_unbox_usize(v_i_3952_);
lean_dec(v_i_3952_);
v_res_3958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3950_, v_sz_boxed_3956_, v_i_boxed_3957_, v_b_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v_as_3950_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(lean_object* v_as_3959_, size_t v_sz_3960_, size_t v_i_3961_, lean_object* v_b_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
uint8_t v___x_3968_; 
v___x_3968_ = lean_usize_dec_lt(v_i_3961_, v_sz_3960_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3962_);
return v___x_3969_;
}
else
{
lean_object* v_snd_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4101_; 
v_snd_3970_ = lean_ctor_get(v_b_3962_, 1);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_b_3962_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v_b_3962_, 0);
lean_dec(v_unused_4102_);
v___x_3972_ = v_b_3962_;
v_isShared_3973_ = v_isSharedCheck_4101_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_snd_3970_);
lean_dec(v_b_3962_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4101_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v_a_3976_; lean_object* v_a_3983_; 
v___x_3974_ = lean_box(0);
v_a_3983_ = lean_array_uget_borrowed(v_as_3959_, v_i_3961_);
if (lean_obj_tag(v_a_3983_) == 0)
{
v_a_3976_ = v_snd_3970_;
goto v___jp_3975_;
}
else
{
lean_object* v_val_3984_; uint8_t v_a_3986_; lean_object* v___f_3989_; lean_object* v___f_3990_; 
v_val_3984_ = lean_ctor_get(v_a_3983_, 0);
v___f_3989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__0));
lean_inc(v_snd_3970_);
v___f_3990_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3990_, 0, v_snd_3970_);
if (lean_obj_tag(v_val_3984_) == 0)
{
lean_object* v_type_3991_; lean_object* v___x_3992_; uint8_t v_fst_3994_; lean_object* v_mctx_3995_; lean_object* v___y_4011_; lean_object* v_mctx_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v_type_3991_ = lean_ctor_get(v_val_3984_, 3);
v___x_3992_ = lean_st_ref_get(v___y_3964_);
v_mctx_4016_ = lean_ctor_get(v___x_3992_, 0);
lean_inc_ref_n(v_mctx_4016_, 2);
lean_dec(v___x_3992_);
v___x_4017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v_mctx_4016_);
v___x_4019_ = l_Lean_Expr_hasFVar(v_type_3991_);
if (v___x_4019_ == 0)
{
uint8_t v___x_4020_; 
v___x_4020_ = l_Lean_Expr_hasMVar(v_type_3991_);
if (v___x_4020_ == 0)
{
lean_dec_ref_known(v___x_4018_, 2);
lean_dec_ref(v___f_3990_);
v_fst_3994_ = v___x_4020_;
v_mctx_3995_ = v_mctx_4016_;
goto v___jp_3993_;
}
else
{
lean_object* v___x_4021_; 
lean_dec_ref(v_mctx_4016_);
lean_inc_ref(v_type_3991_);
v___x_4021_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_3991_, v___x_4018_);
v___y_4011_ = v___x_4021_;
goto v___jp_4010_;
}
}
else
{
lean_object* v___x_4022_; 
lean_dec_ref(v_mctx_4016_);
lean_inc_ref(v_type_3991_);
v___x_4022_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_3991_, v___x_4018_);
v___y_4011_ = v___x_4022_;
goto v___jp_4010_;
}
v___jp_3993_:
{
lean_object* v___x_3996_; lean_object* v_cache_3997_; lean_object* v_zetaDeltaFVarIds_3998_; lean_object* v_postponed_3999_; lean_object* v_diag_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4008_; 
v___x_3996_ = lean_st_ref_take(v___y_3964_);
v_cache_3997_ = lean_ctor_get(v___x_3996_, 1);
v_zetaDeltaFVarIds_3998_ = lean_ctor_get(v___x_3996_, 2);
v_postponed_3999_ = lean_ctor_get(v___x_3996_, 3);
v_diag_4000_ = lean_ctor_get(v___x_3996_, 4);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v___x_3996_, 0);
lean_dec(v_unused_4009_);
v___x_4002_ = v___x_3996_;
v_isShared_4003_ = v_isSharedCheck_4008_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_diag_4000_);
lean_inc(v_postponed_3999_);
lean_inc(v_zetaDeltaFVarIds_3998_);
lean_inc(v_cache_3997_);
lean_dec(v___x_3996_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4008_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_mctx_3995_);
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_mctx_3995_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_cache_3997_);
lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_zetaDeltaFVarIds_3998_);
lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_postponed_3999_);
lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_diag_4000_);
v___x_4005_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_st_ref_put(v___y_3964_, v___x_4005_);
v_a_3986_ = v_fst_3994_;
goto v___jp_3985_;
}
}
}
v___jp_4010_:
{
lean_object* v_snd_4012_; lean_object* v_fst_4013_; lean_object* v_mctx_4014_; uint8_t v___x_4015_; 
v_snd_4012_ = lean_ctor_get(v___y_4011_, 1);
lean_inc(v_snd_4012_);
v_fst_4013_ = lean_ctor_get(v___y_4011_, 0);
lean_inc(v_fst_4013_);
lean_dec_ref(v___y_4011_);
v_mctx_4014_ = lean_ctor_get(v_snd_4012_, 1);
lean_inc_ref(v_mctx_4014_);
lean_dec(v_snd_4012_);
v___x_4015_ = lean_unbox(v_fst_4013_);
lean_dec(v_fst_4013_);
v_fst_3994_ = v___x_4015_;
v_mctx_3995_ = v_mctx_4014_;
goto v___jp_3993_;
}
}
else
{
uint8_t v_nondep_4023_; 
v_nondep_4023_ = lean_ctor_get_uint8(v_val_3984_, sizeof(void*)*5);
if (v_nondep_4023_ == 0)
{
lean_object* v_type_4024_; lean_object* v_value_4025_; lean_object* v___x_4026_; uint8_t v_fst_4028_; lean_object* v_snd_4029_; lean_object* v___y_4046_; uint8_t v_fst_4051_; lean_object* v_snd_4052_; lean_object* v___y_4058_; lean_object* v_mctx_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_type_4024_ = lean_ctor_get(v_val_3984_, 3);
v_value_4025_ = lean_ctor_get(v_val_3984_, 4);
v___x_4026_ = lean_st_ref_get(v___y_3964_);
v_mctx_4062_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_mctx_4062_);
lean_dec(v___x_4026_);
v___x_4063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v_mctx_4062_);
v___x_4065_ = l_Lean_Expr_hasFVar(v_type_4024_);
if (v___x_4065_ == 0)
{
uint8_t v___x_4066_; 
v___x_4066_ = l_Lean_Expr_hasMVar(v_type_4024_);
if (v___x_4066_ == 0)
{
v_fst_4051_ = v___x_4066_;
v_snd_4052_ = v___x_4064_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4067_; 
lean_inc_ref(v_type_4024_);
lean_inc_ref(v___f_3990_);
v___x_4067_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_4024_, v___x_4064_);
v___y_4058_ = v___x_4067_;
goto v___jp_4057_;
}
}
else
{
lean_object* v___x_4068_; 
lean_inc_ref(v_type_4024_);
lean_inc_ref(v___f_3990_);
v___x_4068_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_4024_, v___x_4064_);
v___y_4058_ = v___x_4068_;
goto v___jp_4057_;
}
v___jp_4027_:
{
lean_object* v_mctx_4030_; lean_object* v___x_4031_; lean_object* v_cache_4032_; lean_object* v_zetaDeltaFVarIds_4033_; lean_object* v_postponed_4034_; lean_object* v_diag_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4043_; 
v_mctx_4030_ = lean_ctor_get(v_snd_4029_, 1);
lean_inc_ref(v_mctx_4030_);
lean_dec_ref(v_snd_4029_);
v___x_4031_ = lean_st_ref_take(v___y_3964_);
v_cache_4032_ = lean_ctor_get(v___x_4031_, 1);
v_zetaDeltaFVarIds_4033_ = lean_ctor_get(v___x_4031_, 2);
v_postponed_4034_ = lean_ctor_get(v___x_4031_, 3);
v_diag_4035_ = lean_ctor_get(v___x_4031_, 4);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4043_ == 0)
{
lean_object* v_unused_4044_; 
v_unused_4044_ = lean_ctor_get(v___x_4031_, 0);
lean_dec(v_unused_4044_);
v___x_4037_ = v___x_4031_;
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_diag_4035_);
lean_inc(v_postponed_4034_);
lean_inc(v_zetaDeltaFVarIds_4033_);
lean_inc(v_cache_4032_);
lean_dec(v___x_4031_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v_mctx_4030_);
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_mctx_4030_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_cache_4032_);
lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_zetaDeltaFVarIds_4033_);
lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_postponed_4034_);
lean_ctor_set(v_reuseFailAlloc_4042_, 4, v_diag_4035_);
v___x_4040_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_st_ref_put(v___y_3964_, v___x_4040_);
v_a_3986_ = v_fst_4028_;
goto v___jp_3985_;
}
}
}
v___jp_4045_:
{
lean_object* v_fst_4047_; lean_object* v_snd_4048_; uint8_t v___x_4049_; 
v_fst_4047_ = lean_ctor_get(v___y_4046_, 0);
lean_inc(v_fst_4047_);
v_snd_4048_ = lean_ctor_get(v___y_4046_, 1);
lean_inc(v_snd_4048_);
lean_dec_ref(v___y_4046_);
v___x_4049_ = lean_unbox(v_fst_4047_);
lean_dec(v_fst_4047_);
v_fst_4028_ = v___x_4049_;
v_snd_4029_ = v_snd_4048_;
goto v___jp_4027_;
}
v___jp_4050_:
{
if (v_fst_4051_ == 0)
{
uint8_t v___x_4053_; 
v___x_4053_ = l_Lean_Expr_hasFVar(v_value_4025_);
if (v___x_4053_ == 0)
{
uint8_t v___x_4054_; 
v___x_4054_ = l_Lean_Expr_hasMVar(v_value_4025_);
if (v___x_4054_ == 0)
{
lean_dec_ref(v___f_3990_);
v_fst_4028_ = v___x_4054_;
v_snd_4029_ = v_snd_4052_;
goto v___jp_4027_;
}
else
{
lean_object* v___x_4055_; 
lean_inc_ref(v_value_4025_);
v___x_4055_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_value_4025_, v_snd_4052_);
v___y_4046_ = v___x_4055_;
goto v___jp_4045_;
}
}
else
{
lean_object* v___x_4056_; 
lean_inc_ref(v_value_4025_);
v___x_4056_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_value_4025_, v_snd_4052_);
v___y_4046_ = v___x_4056_;
goto v___jp_4045_;
}
}
else
{
lean_dec_ref(v___f_3990_);
v_fst_4028_ = v_fst_4051_;
v_snd_4029_ = v_snd_4052_;
goto v___jp_4027_;
}
}
v___jp_4057_:
{
lean_object* v_fst_4059_; lean_object* v_snd_4060_; uint8_t v___x_4061_; 
v_fst_4059_ = lean_ctor_get(v___y_4058_, 0);
lean_inc(v_fst_4059_);
v_snd_4060_ = lean_ctor_get(v___y_4058_, 1);
lean_inc(v_snd_4060_);
lean_dec_ref(v___y_4058_);
v___x_4061_ = lean_unbox(v_fst_4059_);
lean_dec(v_fst_4059_);
v_fst_4051_ = v___x_4061_;
v_snd_4052_ = v_snd_4060_;
goto v___jp_4050_;
}
}
else
{
lean_object* v_type_4069_; lean_object* v___x_4070_; uint8_t v_fst_4072_; lean_object* v_mctx_4073_; lean_object* v___y_4089_; lean_object* v_mctx_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v_type_4069_ = lean_ctor_get(v_val_3984_, 3);
v___x_4070_ = lean_st_ref_get(v___y_3964_);
v_mctx_4094_ = lean_ctor_get(v___x_4070_, 0);
lean_inc_ref_n(v_mctx_4094_, 2);
lean_dec(v___x_4070_);
v___x_4095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg___closed__2);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v_mctx_4094_);
v___x_4097_ = l_Lean_Expr_hasFVar(v_type_4069_);
if (v___x_4097_ == 0)
{
uint8_t v___x_4098_; 
v___x_4098_ = l_Lean_Expr_hasMVar(v_type_4069_);
if (v___x_4098_ == 0)
{
lean_dec_ref_known(v___x_4096_, 2);
lean_dec_ref(v___f_3990_);
v_fst_4072_ = v___x_4098_;
v_mctx_4073_ = v_mctx_4094_;
goto v___jp_4071_;
}
else
{
lean_object* v___x_4099_; 
lean_dec_ref(v_mctx_4094_);
lean_inc_ref(v_type_4069_);
v___x_4099_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_4069_, v___x_4096_);
v___y_4089_ = v___x_4099_;
goto v___jp_4088_;
}
}
else
{
lean_object* v___x_4100_; 
lean_dec_ref(v_mctx_4094_);
lean_inc_ref(v_type_4069_);
v___x_4100_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_3990_, v___f_3989_, v_type_4069_, v___x_4096_);
v___y_4089_ = v___x_4100_;
goto v___jp_4088_;
}
v___jp_4071_:
{
lean_object* v___x_4074_; lean_object* v_cache_4075_; lean_object* v_zetaDeltaFVarIds_4076_; lean_object* v_postponed_4077_; lean_object* v_diag_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4086_; 
v___x_4074_ = lean_st_ref_take(v___y_3964_);
v_cache_4075_ = lean_ctor_get(v___x_4074_, 1);
v_zetaDeltaFVarIds_4076_ = lean_ctor_get(v___x_4074_, 2);
v_postponed_4077_ = lean_ctor_get(v___x_4074_, 3);
v_diag_4078_ = lean_ctor_get(v___x_4074_, 4);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v___x_4074_, 0);
lean_dec(v_unused_4087_);
v___x_4080_ = v___x_4074_;
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_diag_4078_);
lean_inc(v_postponed_4077_);
lean_inc(v_zetaDeltaFVarIds_4076_);
lean_inc(v_cache_4075_);
lean_dec(v___x_4074_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4086_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_mctx_4073_);
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_mctx_4073_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_cache_4075_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_zetaDeltaFVarIds_4076_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v_postponed_4077_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v_diag_4078_);
v___x_4083_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_st_ref_put(v___y_3964_, v___x_4083_);
v_a_3986_ = v_fst_4072_;
goto v___jp_3985_;
}
}
}
v___jp_4088_:
{
lean_object* v_snd_4090_; lean_object* v_fst_4091_; lean_object* v_mctx_4092_; uint8_t v___x_4093_; 
v_snd_4090_ = lean_ctor_get(v___y_4089_, 1);
lean_inc(v_snd_4090_);
v_fst_4091_ = lean_ctor_get(v___y_4089_, 0);
lean_inc(v_fst_4091_);
lean_dec_ref(v___y_4089_);
v_mctx_4092_ = lean_ctor_get(v_snd_4090_, 1);
lean_inc_ref(v_mctx_4092_);
lean_dec(v_snd_4090_);
v___x_4093_ = lean_unbox(v_fst_4091_);
lean_dec(v_fst_4091_);
v_fst_4072_ = v___x_4093_;
v_mctx_4073_ = v_mctx_4092_;
goto v___jp_4071_;
}
}
}
v___jp_3985_:
{
if (v_a_3986_ == 0)
{
v_a_3976_ = v_snd_3970_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = l_Lean_LocalDecl_fvarId(v_val_3984_);
v___x_3988_ = lean_array_push(v_snd_3970_, v___x_3987_);
v_a_3976_ = v___x_3988_;
goto v___jp_3975_;
}
}
}
v___jp_3975_:
{
lean_object* v___x_3978_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v_a_3976_);
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3978_ = v___x_3972_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_a_3976_);
v___x_3978_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
size_t v___x_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = ((size_t)1ULL);
v___x_3980_ = lean_usize_add(v_i_3961_, v___x_3979_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_3959_, v_sz_3960_, v___x_3980_, v___x_3978_, v___y_3964_);
return v___x_3981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3___boxed(lean_object* v_as_4103_, lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_b_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
size_t v_sz_boxed_4112_; size_t v_i_boxed_4113_; lean_object* v_res_4114_; 
v_sz_boxed_4112_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4113_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_as_4103_, v_sz_boxed_4112_, v_i_boxed_4113_, v_b_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec_ref(v_as_4103_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(lean_object* v_t_4115_, lean_object* v_init_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_root_4122_; lean_object* v_tail_4123_; lean_object* v___x_4124_; 
v_root_4122_ = lean_ctor_get(v_t_4115_, 0);
v_tail_4123_ = lean_ctor_get(v_t_4115_, 1);
lean_inc_ref(v_init_4116_);
v___x_4124_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2(v_init_4116_, v_root_4122_, v_init_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec_ref(v_init_4116_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4161_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4161_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4161_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
if (lean_obj_tag(v_a_4125_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; 
v_a_4129_ = lean_ctor_get(v_a_4125_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v_a_4125_, 1);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v_a_4129_);
v___x_4131_ = v___x_4127_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; size_t v_sz_4136_; size_t v___x_4137_; lean_object* v___x_4138_; 
lean_del_object(v___x_4127_);
v_a_4133_ = lean_ctor_get(v_a_4125_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v_a_4125_, 1);
v___x_4134_ = lean_box(0);
v___x_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v_a_4133_);
v_sz_4136_ = lean_array_size(v_tail_4123_);
v___x_4137_ = ((size_t)0ULL);
v___x_4138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3(v_tail_4123_, v_sz_4136_, v___x_4137_, v___x_4135_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4152_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4152_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4152_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v_fst_4143_; 
v_fst_4143_ = lean_ctor_get(v_a_4139_, 0);
if (lean_obj_tag(v_fst_4143_) == 0)
{
lean_object* v_snd_4144_; lean_object* v___x_4146_; 
v_snd_4144_ = lean_ctor_get(v_a_4139_, 1);
lean_inc(v_snd_4144_);
lean_dec(v_a_4139_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v_snd_4144_);
v___x_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_snd_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
else
{
lean_object* v_val_4148_; lean_object* v___x_4150_; 
lean_inc_ref(v_fst_4143_);
lean_dec(v_a_4139_);
v_val_4148_ = lean_ctor_get(v_fst_4143_, 0);
lean_inc(v_val_4148_);
lean_dec_ref_known(v_fst_4143_, 1);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v_val_4148_);
v___x_4150_ = v___x_4141_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_val_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
v_a_4153_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4138_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4138_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
v_a_4162_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4124_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4124_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1___boxed(lean_object* v_t_4170_, lean_object* v_init_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_t_4170_, v_init_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_t_4170_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(lean_object* v_goal_4178_, lean_object* v_fvarIds_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v___x_4185_; 
lean_inc(v_goal_4178_);
v___x_4185_ = l_Lean_MVarId_getDecl(v_goal_4178_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v_lctx_4187_; lean_object* v_decls_4188_; lean_object* v___x_4189_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v_lctx_4187_ = lean_ctor_get(v_a_4186_, 1);
lean_inc_ref(v_lctx_4187_);
lean_dec(v_a_4186_);
v_decls_4188_ = lean_ctor_get(v_lctx_4187_, 1);
lean_inc_ref(v_decls_4188_);
lean_dec_ref(v_lctx_4187_);
v___x_4189_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1(v_decls_4188_, v_fvarIds_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
lean_dec_ref(v_decls_4188_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l_Lean_MVarId_tryClearMany(v_goal_4178_, v_a_4190_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
lean_dec(v_a_4190_);
return v___x_4191_;
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_goal_4178_);
v_a_4192_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4189_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4189_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v_fvarIds_4179_);
lean_dec(v_goal_4178_);
v_a_4200_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4185_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4185_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27___boxed(lean_object* v_goal_4208_, lean_object* v_fvarIds_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_goal_4208_, v_fvarIds_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(lean_object* v_as_4216_, size_t v_sz_4217_, size_t v_i_4218_, lean_object* v_b_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___redArg(v_as_4216_, v_sz_4217_, v_i_4218_, v_b_4219_, v___y_4221_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6___boxed(lean_object* v_as_4226_, lean_object* v_sz_4227_, lean_object* v_i_4228_, lean_object* v_b_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
size_t v_sz_boxed_4235_; size_t v_i_boxed_4236_; lean_object* v_res_4237_; 
v_sz_boxed_4235_ = lean_unbox_usize(v_sz_4227_);
lean_dec(v_sz_4227_);
v_i_boxed_4236_ = lean_unbox_usize(v_i_4228_);
lean_dec(v_i_4228_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__3_spec__6(v_as_4226_, v_sz_boxed_4235_, v_i_boxed_4236_, v_b_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec_ref(v_as_4226_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___redArg(v_as_4238_, v_sz_4239_, v_i_4240_, v_b_4241_, v___y_4243_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_as_4248_, lean_object* v_sz_4249_, lean_object* v_i_4250_, lean_object* v_b_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
size_t v_sz_boxed_4257_; size_t v_i_boxed_4258_; lean_object* v_res_4259_; 
v_sz_boxed_4257_ = lean_unbox_usize(v_sz_4249_);
lean_dec(v_sz_4249_);
v_i_boxed_4258_ = lean_unbox_usize(v_i_4250_);
lean_dec(v_i_4250_);
v_res_4259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27_spec__1_spec__2_spec__4_spec__5(v_as_4248_, v_sz_boxed_4257_, v_i_boxed_4258_, v_b_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec_ref(v_as_4248_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(lean_object* v_fs_4260_, lean_object* v_as_4261_, size_t v_sz_4262_, size_t v_i_4263_, lean_object* v_b_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v___x_4272_; 
v___x_4272_ = lean_usize_dec_lt(v_i_4263_, v_sz_4262_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; 
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_b_4264_);
return v___x_4273_;
}
else
{
lean_object* v_a_4274_; lean_object* v_fst_4275_; lean_object* v_snd_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v_a_4274_ = lean_array_uget_borrowed(v_as_4261_, v_i_4263_);
v_fst_4275_ = lean_ctor_get(v_a_4274_, 0);
v_snd_4276_ = lean_ctor_get(v_a_4274_, 1);
lean_inc(v_snd_4276_);
v___x_4277_ = l_Lean_Meta_FVarSubst_get(v_fs_4260_, v_snd_4276_);
lean_inc(v_fst_4275_);
v___x_4278_ = l_Lean_Elab_Term_addLocalVarInfo(v_fst_4275_, v___x_4277_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v___x_4279_; size_t v___x_4280_; size_t v___x_4281_; 
lean_dec_ref_known(v___x_4278_, 1);
v___x_4279_ = lean_box(0);
v___x_4280_ = ((size_t)1ULL);
v___x_4281_ = lean_usize_add(v_i_4263_, v___x_4280_);
v_i_4263_ = v___x_4281_;
v_b_4264_ = v___x_4279_;
goto _start;
}
else
{
return v___x_4278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1___boxed(lean_object* v_fs_4283_, lean_object* v_as_4284_, lean_object* v_sz_4285_, lean_object* v_i_4286_, lean_object* v_b_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
size_t v_sz_boxed_4295_; size_t v_i_boxed_4296_; lean_object* v_res_4297_; 
v_sz_boxed_4295_ = lean_unbox_usize(v_sz_4285_);
lean_dec(v_sz_4285_);
v_i_boxed_4296_ = lean_unbox_usize(v_i_4286_);
lean_dec(v_i_4286_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4283_, v_as_4284_, v_sz_boxed_4295_, v_i_boxed_4296_, v_b_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_as_4284_);
lean_dec(v_fs_4283_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(lean_object* v_fs_4298_, lean_object* v_toTag_4299_, size_t v_sz_4300_, size_t v___x_4301_, lean_object* v___x_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__1(v_fs_4298_, v_toTag_4299_, v_sz_4300_, v___x_4301_, v___x_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; 
v_unused_4318_ = lean_ctor_get(v___x_4310_, 0);
lean_dec(v_unused_4318_);
v___x_4312_ = v___x_4310_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_dec(v___x_4310_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v___x_4302_);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4302_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
else
{
return v___x_4310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed(lean_object* v_fs_4319_, lean_object* v_toTag_4320_, lean_object* v_sz_4321_, lean_object* v___x_4322_, lean_object* v___x_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
size_t v_sz_boxed_4331_; size_t v___x_1633__boxed_4332_; lean_object* v_res_4333_; 
v_sz_boxed_4331_ = lean_unbox_usize(v_sz_4321_);
lean_dec(v_sz_4321_);
v___x_1633__boxed_4332_ = lean_unbox_usize(v___x_4322_);
lean_dec(v___x_4322_);
v_res_4333_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0(v_fs_4319_, v_toTag_4320_, v_sz_boxed_4331_, v___x_1633__boxed_4332_, v___x_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v_toTag_4320_);
lean_dec(v_fs_4319_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(lean_object* v_as_4334_, size_t v_i_4335_, size_t v_stop_4336_, lean_object* v_b_4337_){
_start:
{
lean_object* v___y_4339_; uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_eq(v_i_4335_, v_stop_4336_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4344_ = lean_array_uget_borrowed(v_as_4334_, v_i_4335_);
v___x_4345_ = l_Lean_Expr_isFVar(v___x_4344_);
if (v___x_4345_ == 0)
{
v___y_4339_ = v_b_4337_;
goto v___jp_4338_;
}
else
{
lean_object* v___x_4346_; 
lean_inc(v___x_4344_);
v___x_4346_ = lean_array_push(v_b_4337_, v___x_4344_);
v___y_4339_ = v___x_4346_;
goto v___jp_4338_;
}
}
else
{
return v_b_4337_;
}
v___jp_4338_:
{
size_t v___x_4340_; size_t v___x_4341_; 
v___x_4340_ = ((size_t)1ULL);
v___x_4341_ = lean_usize_add(v_i_4335_, v___x_4340_);
v_i_4335_ = v___x_4341_;
v_b_4337_ = v___y_4339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3___boxed(lean_object* v_as_4347_, lean_object* v_i_4348_, lean_object* v_stop_4349_, lean_object* v_b_4350_){
_start:
{
size_t v_i_boxed_4351_; size_t v_stop_boxed_4352_; lean_object* v_res_4353_; 
v_i_boxed_4351_ = lean_unbox_usize(v_i_4348_);
lean_dec(v_i_4348_);
v_stop_boxed_4352_ = lean_unbox_usize(v_stop_4349_);
lean_dec(v_stop_4349_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v_as_4347_, v_i_boxed_4351_, v_stop_boxed_4352_, v_b_4350_);
lean_dec_ref(v_as_4347_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(lean_object* v_fs_4354_, size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_bs_4357_){
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
v___x_4362_ = l_Lean_Meta_FVarSubst_get(v_fs_4354_, v_v_4359_);
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4356_, v___x_4363_);
v___x_4365_ = lean_array_uset(v_bs_x27_4361_, v_i_4356_, v___x_4362_);
v_i_4356_ = v___x_4364_;
v_bs_4357_ = v___x_4365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2___boxed(lean_object* v_fs_4367_, lean_object* v_sz_4368_, lean_object* v_i_4369_, lean_object* v_bs_4370_){
_start:
{
size_t v_sz_boxed_4371_; size_t v_i_boxed_4372_; lean_object* v_res_4373_; 
v_sz_boxed_4371_ = lean_unbox_usize(v_sz_4368_);
lean_dec(v_sz_4368_);
v_i_boxed_4372_ = lean_unbox_usize(v_i_4369_);
lean_dec(v_i_4369_);
v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4367_, v_sz_boxed_4371_, v_i_boxed_4372_, v_bs_4370_);
lean_dec(v_fs_4367_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(size_t v_sz_4374_, size_t v_i_4375_, lean_object* v_bs_4376_){
_start:
{
uint8_t v___x_4377_; 
v___x_4377_ = lean_usize_dec_lt(v_i_4375_, v_sz_4374_);
if (v___x_4377_ == 0)
{
return v_bs_4376_;
}
else
{
lean_object* v_v_4378_; lean_object* v___x_4379_; lean_object* v_bs_x27_4380_; lean_object* v___x_4381_; size_t v___x_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
v_v_4378_ = lean_array_uget(v_bs_4376_, v_i_4375_);
v___x_4379_ = lean_unsigned_to_nat(0u);
v_bs_x27_4380_ = lean_array_uset(v_bs_4376_, v_i_4375_, v___x_4379_);
v___x_4381_ = l_Lean_Expr_fvarId_x21(v_v_4378_);
lean_dec(v_v_4378_);
v___x_4382_ = ((size_t)1ULL);
v___x_4383_ = lean_usize_add(v_i_4375_, v___x_4382_);
v___x_4384_ = lean_array_uset(v_bs_x27_4380_, v_i_4375_, v___x_4381_);
v_i_4375_ = v___x_4383_;
v_bs_4376_ = v___x_4384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0___boxed(lean_object* v_sz_4386_, lean_object* v_i_4387_, lean_object* v_bs_4388_){
_start:
{
size_t v_sz_boxed_4389_; size_t v_i_boxed_4390_; lean_object* v_res_4391_; 
v_sz_boxed_4389_ = lean_unbox_usize(v_sz_4386_);
lean_dec(v_sz_4386_);
v_i_boxed_4390_ = lean_unbox_usize(v_i_4387_);
lean_dec(v_i_4387_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_boxed_4389_, v_i_boxed_4390_, v_bs_4388_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(lean_object* v_toTag_4396_, lean_object* v_g_4397_, lean_object* v_fs_4398_, lean_object* v_clears_4399_, lean_object* v_gs_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v___y_4409_; size_t v_sz_4446_; size_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; uint8_t v___x_4452_; 
v_sz_4446_ = lean_array_size(v_clears_4399_);
v___x_4447_ = ((size_t)0ULL);
v___x_4448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__2(v_fs_4398_, v_sz_4446_, v___x_4447_, v_clears_4399_);
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = lean_array_get_size(v___x_4448_);
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___closed__0));
v___x_4452_ = lean_nat_dec_lt(v___x_4449_, v___x_4450_);
if (v___x_4452_ == 0)
{
lean_dec_ref(v___x_4448_);
v___y_4409_ = v___x_4451_;
goto v___jp_4408_;
}
else
{
uint8_t v___x_4453_; 
v___x_4453_ = lean_nat_dec_le(v___x_4450_, v___x_4450_);
if (v___x_4453_ == 0)
{
if (v___x_4452_ == 0)
{
lean_dec_ref(v___x_4448_);
v___y_4409_ = v___x_4451_;
goto v___jp_4408_;
}
else
{
size_t v___x_4454_; lean_object* v___x_4455_; 
v___x_4454_ = lean_usize_of_nat(v___x_4450_);
v___x_4455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4448_, v___x_4447_, v___x_4454_, v___x_4451_);
lean_dec_ref(v___x_4448_);
v___y_4409_ = v___x_4455_;
goto v___jp_4408_;
}
}
else
{
size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_usize_of_nat(v___x_4450_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__3(v___x_4448_, v___x_4447_, v___x_4456_, v___x_4451_);
lean_dec_ref(v___x_4448_);
v___y_4409_ = v___x_4457_;
goto v___jp_4408_;
}
}
v___jp_4408_:
{
size_t v_sz_4410_; size_t v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_sz_4410_ = lean_array_size(v___y_4409_);
v___x_4411_ = ((size_t)0ULL);
v___x_4412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish_spec__0(v_sz_4410_, v___x_4411_, v___y_4409_);
v___x_4413_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_tryClearMany_x27(v_g_4397_, v___x_4412_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; size_t v_sz_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___f_4419_; lean_object* v___x_4420_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc_n(v_a_4414_, 2);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = lean_box(0);
v_sz_4416_ = lean_array_size(v_toTag_4396_);
v___x_4417_ = lean_box_usize(v_sz_4416_);
v___x_4418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed__const__1));
v___f_4419_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4419_, 0, v_fs_4398_);
lean_closure_set(v___f_4419_, 1, v_toTag_4396_);
lean_closure_set(v___f_4419_, 2, v___x_4417_);
lean_closure_set(v___f_4419_, 3, v___x_4418_);
lean_closure_set(v___f_4419_, 4, v___x_4415_);
v___x_4420_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_a_4414_, v___f_4419_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4428_; 
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; 
v_unused_4429_ = lean_ctor_get(v___x_4420_, 0);
lean_dec(v_unused_4429_);
v___x_4422_ = v___x_4420_;
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
else
{
lean_dec(v___x_4420_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = lean_array_push(v_gs_4400_, v_a_4414_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4424_);
v___x_4426_ = v___x_4422_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4414_);
lean_dec_ref(v_gs_4400_);
v_a_4430_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4420_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4420_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec_ref(v_gs_4400_);
lean_dec(v_fs_4398_);
lean_dec_ref(v_toTag_4396_);
v_a_4438_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4413_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4413_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish___boxed(lean_object* v_toTag_4458_, lean_object* v_g_4459_, lean_object* v_fs_4460_, lean_object* v_clears_4461_, lean_object* v_gs_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_finish(v_toTag_4458_, v_g_4459_, v_fs_4460_, v_clears_4461_, v_gs_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4470_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = lean_box(0);
v___x_4472_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
lean_ctor_set(v___x_4473_, 1, v___x_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___boxed(lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(lean_object* v_00_u03b1_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___boxed(lean_object* v_00_u03b1_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0(v_00_u03b1_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(lean_object* v_stx_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_stx_4531_);
v___x_4538_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
lean_inc(v_stx_4531_);
v___x_4540_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__1));
lean_inc(v_stx_4531_);
v___x_4542_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4543_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__4));
lean_inc(v_stx_4531_);
v___x_4544_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__3));
lean_inc(v_stx_4531_);
v___x_4546_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__5));
lean_inc(v_stx_4531_);
v___x_4548_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4547_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__7));
lean_inc(v_stx_4531_);
v___x_4550_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
lean_inc(v_stx_4531_);
v___x_4552_ = l_Lean_Syntax_isOfKind(v_stx_4531_, v___x_4551_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; 
lean_dec(v_stx_4531_);
v___x_4553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = lean_unsigned_to_nat(1u);
v___x_4555_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4554_);
v___x_4556_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4555_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4565_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4559_ = v___x_4556_;
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4565_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v_stx_4531_);
lean_ctor_set(v___x_4561_, 1, v_a_4557_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4561_);
v___x_4563_ = v___x_4559_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
else
{
lean_dec(v_stx_4531_);
return v___x_4556_;
}
}
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_ps_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4566_ = lean_unsigned_to_nat(1u);
v___x_4567_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4566_);
v_ps_4568_ = l_Lean_Syntax_getArgs(v___x_4567_);
lean_dec(v___x_4567_);
v___x_4569_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4568_);
lean_dec_ref(v_ps_4568_);
v___x_4570_ = lean_array_to_list(v___x_4569_);
v___x_4571_ = lean_box(0);
v___x_4572_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4570_, v___x_4571_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
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
v___x_4577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4577_, 0, v_stx_4531_);
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
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec(v_stx_4531_);
v_a_4582_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4572_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4572_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
else
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4590_ = lean_unsigned_to_nat(1u);
v___x_4591_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4590_);
v___x_4592_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4591_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4601_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4595_ = v___x_4592_;
v_isShared_4596_ = v_isSharedCheck_4601_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4592_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4601_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; lean_object* v___x_4599_; 
v___x_4597_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4597_, 0, v_stx_4531_);
lean_ctor_set(v___x_4597_, 1, v_a_4593_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4597_);
v___x_4599_ = v___x_4595_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
else
{
lean_dec(v_stx_4531_);
return v___x_4592_;
}
}
}
else
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4602_, 0, v_stx_4531_);
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
}
else
{
lean_object* v___x_4604_; lean_object* v_h_4605_; 
v___x_4604_ = lean_unsigned_to_nat(0u);
v_h_4605_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4604_);
lean_dec(v_stx_4531_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4610_; uint8_t v___x_4611_; 
v___x_4610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__11));
lean_inc(v_h_4605_);
v___x_4611_ = l_Lean_Syntax_isOfKind(v_h_4605_, v___x_4610_);
if (v___x_4611_ == 0)
{
lean_object* v___x_4612_; 
lean_dec(v_h_4605_);
v___x_4612_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4612_;
}
else
{
goto v___jp_4606_;
}
}
else
{
goto v___jp_4606_;
}
v___jp_4606_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = l_Lean_TSyntax_getId(v_h_4605_);
v___x_4608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4608_, 0, v_h_4605_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
return v___x_4609_;
}
}
}
else
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___x_4614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4614_, 0, v_stx_4531_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4616_);
if (v___x_4538_ == 0)
{
uint8_t v___x_4637_; 
lean_inc(v___x_4617_);
v___x_4637_ = l_Lean_Syntax_isOfKind(v___x_4617_, v___x_4537_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
lean_dec(v___x_4617_);
lean_dec(v_stx_4531_);
v___x_4638_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4638_;
}
else
{
goto v___jp_4618_;
}
}
else
{
goto v___jp_4618_;
}
v___jp_4618_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4619_ = lean_unsigned_to_nat(1u);
v___x_4620_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4619_);
v___x_4621_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4620_);
v___x_4622_ = l_Lean_Syntax_matchesNull(v___x_4620_, v___x_4621_);
if (v___x_4622_ == 0)
{
uint8_t v___x_4623_; 
lean_dec(v_stx_4531_);
v___x_4623_ = l_Lean_Syntax_matchesNull(v___x_4620_, v___x_4616_);
if (v___x_4623_ == 0)
{
lean_object* v___x_4624_; 
lean_dec(v___x_4617_);
v___x_4624_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg();
return v___x_4624_;
}
else
{
v_stx_4531_ = v___x_4617_;
goto _start;
}
}
else
{
lean_object* v___x_4626_; 
v___x_4626_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_4617_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4636_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v_t_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v_t_4631_ = l_Lean_Syntax_getArg(v___x_4620_, v___x_4619_);
lean_dec(v___x_4620_);
v___x_4632_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_4632_, 0, v_stx_4531_);
lean_ctor_set(v___x_4632_, 1, v_a_4627_);
lean_ctor_set(v___x_4632_, 2, v_t_4631_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4632_);
v___x_4634_ = v___x_4629_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
else
{
lean_dec(v___x_4620_);
lean_dec(v_stx_4531_);
return v___x_4626_;
}
}
}
}
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v_ps_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4639_ = lean_unsigned_to_nat(0u);
v___x_4640_ = l_Lean_Syntax_getArg(v_stx_4531_, v___x_4639_);
v_ps_4641_ = l_Lean_Syntax_getArgs(v___x_4640_);
lean_dec(v___x_4640_);
v___x_4642_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ps_4641_);
lean_dec_ref(v_ps_4641_);
v___x_4643_ = lean_array_to_list(v___x_4642_);
v___x_4644_ = lean_box(0);
v___x_4645_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__1(v___x_4643_, v___x_4644_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
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
v___x_4650_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_alts_x27(v_stx_4531_, v_a_4646_);
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
lean_dec(v_stx_4531_);
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
lean_object* v_a_4725_; lean_object* v_expr_4726_; lean_object* v_hName_x3f_4727_; lean_object* v___x_4728_; uint8_t v___y_4739_; uint8_t v___x_4742_; 
v_a_4725_ = lean_array_uget_borrowed(v_as_4708_, v_i_4710_);
v_expr_4726_ = lean_ctor_get(v_a_4725_, 0);
v_hName_x3f_4727_ = lean_ctor_get(v_a_4725_, 2);
v___x_4728_ = lean_box(0);
v___x_4742_ = l_Lean_Expr_isFVar(v_expr_4726_);
if (v___x_4742_ == 0)
{
v___y_4739_ = v___x_4742_;
goto v___jp_4738_;
}
else
{
if (lean_obj_tag(v_hName_x3f_4727_) == 0)
{
v___y_4739_ = v___x_4742_;
goto v___jp_4738_;
}
else
{
goto v___jp_4729_;
}
}
v___jp_4729_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4730_ = lean_array_get_borrowed(v___x_4728_, v_fst_4707_, v_snd_4721_);
lean_inc(v___x_4730_);
v___x_4731_ = l_Lean_mkFVar(v___x_4730_);
v___x_4732_ = lean_array_push(v_fst_4720_, v___x_4731_);
v___x_4733_ = lean_unsigned_to_nat(1u);
v___x_4734_ = lean_nat_add(v_snd_4721_, v___x_4733_);
lean_dec(v_snd_4721_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 1, v___x_4734_);
lean_ctor_set(v___x_4723_, 0, v___x_4732_);
v___x_4736_ = v___x_4723_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4732_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
v_a_4714_ = v___x_4736_;
goto v___jp_4713_;
}
}
v___jp_4738_:
{
if (v___y_4739_ == 0)
{
goto v___jp_4729_;
}
else
{
lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_del_object(v___x_4723_);
lean_inc_ref(v_expr_4726_);
v___x_4740_ = lean_array_push(v_fst_4720_, v_expr_4726_);
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
v___x_4796_ = l_Array_toSubarray___redArg(v___y_4793_, v_lower_4794_, v_upper_4795_);
v___x_4797_ = l_Subarray_copy___redArg(v___x_4796_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
lean_ctor_set(v___x_4798_, 1, v___y_4791_);
v___x_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___y_4792_);
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
v___y_4791_ = v_snd_4808_;
v___y_4792_ = v_fst_4814_;
v___y_4793_ = v_fst_4807_;
v_lower_4794_ = v_snd_4815_;
v_upper_4795_ = v___x_4816_;
goto v___jp_4790_;
}
else
{
lean_dec(v_snd_4815_);
v___y_4791_ = v_snd_4808_;
v___y_4792_ = v_fst_4814_;
v___y_4793_ = v_fst_4807_;
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
v___y_4929_ = v___x_4962_;
v___y_4930_ = v_a_4961_;
v___y_4931_ = v_fst_4949_;
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
v___y_4929_ = v___x_4962_;
v___y_4930_ = v_a_4961_;
v___y_4931_ = v_fst_4949_;
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
lean_ctor_set(v___x_4933_, 0, v___y_4930_);
lean_ctor_set(v___x_4933_, 1, v___y_4929_);
lean_ctor_set(v___x_4933_, 2, v___y_4932_);
v___x_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___y_4931_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(lean_object* v___x_5129_, size_t v_sz_5130_, size_t v_i_5131_, lean_object* v_bs_5132_){
_start:
{
uint8_t v___x_5133_; 
v___x_5133_ = lean_usize_dec_lt(v_i_5131_, v_sz_5130_);
if (v___x_5133_ == 0)
{
return v_bs_5132_;
}
else
{
lean_object* v___x_5134_; uint8_t v___x_5135_; lean_object* v___x_5136_; lean_object* v_bs_x27_5137_; uint8_t v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; size_t v___x_5141_; size_t v___x_5142_; lean_object* v___x_5143_; 
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = lean_nat_dec_eq(v___x_5129_, v___x_5134_);
v___x_5136_ = lean_unsigned_to_nat(0u);
v_bs_x27_5137_ = lean_array_uset(v_bs_5132_, v_i_5131_, v___x_5136_);
v___x_5138_ = 0;
v___x_5139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg___lam__5___closed__1));
v___x_5140_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_5140_, 0, v___x_5139_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1, v___x_5138_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 1, v___x_5135_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 2, v___x_5135_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 3, v___x_5135_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 4, v___x_5135_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 5, v___x_5135_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 6, v___x_5135_);
v___x_5141_ = ((size_t)1ULL);
v___x_5142_ = lean_usize_add(v_i_5131_, v___x_5141_);
v___x_5143_ = lean_array_uset(v_bs_x27_5137_, v_i_5131_, v___x_5140_);
v_i_5131_ = v___x_5142_;
v_bs_5132_ = v___x_5143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2___boxed(lean_object* v___x_5145_, lean_object* v_sz_5146_, lean_object* v_i_5147_, lean_object* v_bs_5148_){
_start:
{
size_t v_sz_boxed_5149_; size_t v_i_boxed_5150_; lean_object* v_res_5151_; 
v_sz_boxed_5149_ = lean_unbox_usize(v_sz_5146_);
lean_dec(v_sz_5146_);
v_i_boxed_5150_ = lean_unbox_usize(v_i_5147_);
lean_dec(v_i_5147_);
v_res_5151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5145_, v_sz_boxed_5149_, v_i_boxed_5150_, v_bs_5148_);
lean_dec(v___x_5145_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1(uint8_t v___x_5152_, lean_object* v___x_5153_, lean_object* v_pat_5154_, lean_object* v_tgts_5155_, lean_object* v___x_5156_, lean_object* v___f_5157_, lean_object* v_g_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
if (v___x_5152_ == 0)
{
lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___y_5169_; 
lean_dec(v_g_5158_);
v___x_5166_ = lean_unsigned_to_nat(1u);
v___x_5167_ = lean_nat_dec_eq(v___x_5153_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v_ref_5178_; 
v_ref_5178_ = lean_ctor_get(v_pat_5154_, 0);
lean_inc(v_ref_5178_);
v___y_5169_ = v_ref_5178_;
goto v___jp_5168_;
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec_ref(v_tgts_5155_);
v___x_5179_ = lean_box(0);
v___x_5180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5180_, 0, v_pat_5154_);
lean_ctor_set(v___x_5180_, 1, v___x_5179_);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc(v___y_5160_);
lean_inc_ref(v___y_5159_);
v___x_5181_ = lean_apply_8(v___f_5157_, v___x_5180_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, lean_box(0));
return v___x_5181_;
}
v___jp_5168_:
{
lean_object* v___x_5170_; lean_object* v_snd_5171_; size_t v_sz_5172_; size_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v_snd_5176_; lean_object* v___x_5177_; 
v___x_5170_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_asTuple(v_pat_5154_);
v_snd_5171_ = lean_ctor_get(v___x_5170_, 1);
lean_inc(v_snd_5171_);
lean_dec_ref(v___x_5170_);
v_sz_5172_ = lean_array_size(v_tgts_5155_);
v___x_5173_ = ((size_t)0ULL);
v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_RCases_rcases_spec__2(v___x_5153_, v_sz_5172_, v___x_5173_, v_tgts_5155_);
v___x_5175_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructor(v___y_5169_, v___x_5174_, v___x_5167_, v___x_5156_, v_snd_5171_);
lean_dec_ref(v___x_5174_);
v_snd_5176_ = lean_ctor_get(v___x_5175_, 1);
lean_inc(v_snd_5176_);
lean_dec_ref(v___x_5175_);
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
lean_inc(v___y_5160_);
lean_inc_ref(v___y_5159_);
v___x_5177_ = lean_apply_8(v___f_5157_, v_snd_5176_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, lean_box(0));
return v___x_5177_;
}
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
lean_dec_ref(v___f_5157_);
lean_dec_ref(v_tgts_5155_);
lean_dec_ref(v_pat_5154_);
v___x_5182_ = lean_box(0);
v___x_5183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5183_, 0, v_g_5158_);
lean_ctor_set(v___x_5183_, 1, v___x_5182_);
v___x_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5183_);
return v___x_5184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed(lean_object* v___x_5185_, lean_object* v___x_5186_, lean_object* v_pat_5187_, lean_object* v_tgts_5188_, lean_object* v___x_5189_, lean_object* v___f_5190_, lean_object* v_g_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
uint8_t v___x_5349__boxed_5199_; lean_object* v_res_5200_; 
v___x_5349__boxed_5199_ = lean_unbox(v___x_5185_);
v_res_5200_ = l_Lean_Elab_Tactic_RCases_rcases___lam__1(v___x_5349__boxed_5199_, v___x_5186_, v_pat_5187_, v_tgts_5188_, v___x_5189_, v___f_5190_, v_g_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___x_5189_);
lean_dec(v___x_5186_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases(lean_object* v_tgts_5201_, lean_object* v_pat_5202_, lean_object* v_g_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v___f_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; uint8_t v___x_5214_; lean_object* v___x_5215_; lean_object* v___y_5216_; uint8_t v___x_5217_; lean_object* v___x_5218_; 
lean_inc(v_g_5203_);
lean_inc_ref(v_tgts_5201_);
v___f_5211_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5211_, 0, v_tgts_5201_);
lean_closure_set(v___f_5211_, 1, v_g_5203_);
v___x_5212_ = lean_array_get_size(v_tgts_5201_);
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_nat_dec_eq(v___x_5212_, v___x_5213_);
v___x_5215_ = lean_box(v___x_5214_);
v___y_5216_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rcases___lam__1___boxed), 14, 7);
lean_closure_set(v___y_5216_, 0, v___x_5215_);
lean_closure_set(v___y_5216_, 1, v___x_5212_);
lean_closure_set(v___y_5216_, 2, v_pat_5202_);
lean_closure_set(v___y_5216_, 3, v_tgts_5201_);
lean_closure_set(v___y_5216_, 4, v___x_5213_);
lean_closure_set(v___y_5216_, 5, v___f_5211_);
lean_closure_set(v___y_5216_, 6, v_g_5203_);
v___x_5217_ = 1;
v___x_5218_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___y_5216_, v___x_5217_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rcases___boxed(lean_object* v_tgts_5219_, lean_object* v_pat_5220_, lean_object* v_g_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_Elab_Tactic_RCases_rcases(v_tgts_5219_, v_pat_5220_, v_g_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(lean_object* v_ty_5234_, lean_object* v_g_5235_, lean_object* v_pat_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_Elab_Term_elabType(v_ty_5234_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_object* v_a_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
lean_inc_n(v_a_5245_, 2);
lean_dec_ref_known(v___x_5244_, 1);
v___x_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5246_, 0, v_a_5245_);
v___x_5247_ = 0;
v___x_5248_ = lean_box(0);
v___x_5249_ = l_Lean_Meta_mkFreshExprMVar(v___x_5246_, v___x_5247_, v___x_5248_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___y_5252_; lean_object* v___x_5306_; 
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
lean_inc(v_a_5250_);
lean_dec_ref_known(v___x_5249_, 1);
v___x_5306_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v_pat_5236_);
if (lean_obj_tag(v___x_5306_) == 0)
{
v___y_5252_ = v___x_5248_;
goto v___jp_5251_;
}
else
{
lean_object* v_val_5307_; 
v_val_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_val_5307_);
lean_dec_ref_known(v___x_5306_, 1);
v___y_5252_ = v_val_5307_;
goto v___jp_5251_;
}
v___jp_5251_:
{
lean_object* v___x_5253_; 
lean_inc(v_a_5250_);
v___x_5253_ = l_Lean_MVarId_assert(v_g_5235_, v___y_5252_, v_a_5245_, v_a_5250_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; uint8_t v___x_5255_; lean_object* v___x_5256_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
lean_inc(v_a_5254_);
lean_dec_ref_known(v___x_5253_, 1);
v___x_5255_ = 0;
v___x_5256_ = l_Lean_Meta_intro1Core(v_a_5254_, v___x_5255_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v_fst_5258_; lean_object* v_snd_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5289_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_a_5257_);
lean_dec_ref_known(v___x_5256_, 1);
v_fst_5258_ = lean_ctor_get(v_a_5257_, 0);
v_snd_5259_ = lean_ctor_get(v_a_5257_, 1);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_a_5257_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5261_ = v_a_5257_;
v_isShared_5262_ = v_isSharedCheck_5289_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_snd_5259_);
lean_inc(v_fst_5258_);
lean_dec(v_a_5257_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5289_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5263_ = lean_box(0);
v___x_5264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5265_ = l_Lean_Expr_fvar___override(v_fst_5258_);
v___x_5266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___x_5267_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5259_, v___x_5263_, v___x_5264_, v___x_5265_, v___x_5264_, v_pat_5236_, v___x_5266_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec_ref(v___x_5265_);
if (lean_obj_tag(v___x_5267_) == 0)
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5280_; 
v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5267_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5270_ = v___x_5267_;
v_isShared_5271_ = v_isSharedCheck_5280_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5267_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5280_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5275_; 
v___x_5272_ = l_Lean_Expr_mvarId_x21(v_a_5250_);
lean_dec(v_a_5250_);
v___x_5273_ = lean_array_to_list(v_a_5268_);
if (v_isShared_5262_ == 0)
{
lean_ctor_set_tag(v___x_5261_, 1);
lean_ctor_set(v___x_5261_, 1, v___x_5273_);
lean_ctor_set(v___x_5261_, 0, v___x_5272_);
v___x_5275_ = v___x_5261_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5272_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5277_; 
if (v_isShared_5271_ == 0)
{
lean_ctor_set(v___x_5270_, 0, v___x_5275_);
v___x_5277_ = v___x_5270_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5275_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_del_object(v___x_5261_);
lean_dec(v_a_5250_);
v_a_5281_ = lean_ctor_get(v___x_5267_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5267_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5267_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5267_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
lean_dec(v_a_5250_);
lean_dec_ref(v_pat_5236_);
v_a_5290_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5256_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5256_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec(v_a_5250_);
lean_dec_ref(v_pat_5236_);
v_a_5298_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5253_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5253_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec(v_a_5245_);
lean_dec_ref(v_pat_5236_);
lean_dec(v_g_5235_);
v_a_5308_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5249_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5249_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
lean_dec_ref(v_pat_5236_);
lean_dec(v_g_5235_);
v_a_5316_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5244_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5244_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed(lean_object* v_ty_5324_, lean_object* v_g_5325_, lean_object* v_pat_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0(v_ty_5324_, v_g_5325_, v_pat_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(lean_object* v_pat_5335_, lean_object* v_ty_5336_, lean_object* v_g_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_){
_start:
{
lean_object* v___f_5345_; uint8_t v___x_5346_; lean_object* v___x_5347_; 
v___f_5345_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5345_, 0, v_ty_5336_);
lean_closure_set(v___f_5345_, 1, v_g_5337_);
lean_closure_set(v___f_5345_, 2, v_pat_5335_);
v___x_5346_ = 1;
v___x_5347_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5345_, v___x_5346_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___boxed(lean_object* v_pat_5348_, lean_object* v_ty_5349_, lean_object* v_g_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v_pat_5348_, v_ty_5349_, v_g_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats(lean_object* v_pats_5366_, lean_object* v_acc_5367_, lean_object* v_ty_x3f_5368_){
_start:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; 
v___x_5369_ = lean_unsigned_to_nat(0u);
v___x_5370_ = lean_array_get_size(v_pats_5366_);
v___x_5371_ = lean_nat_dec_lt(v___x_5369_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_dec(v_ty_x3f_5368_);
return v_acc_5367_;
}
else
{
uint8_t v___x_5372_; 
v___x_5372_ = lean_nat_dec_le(v___x_5370_, v___x_5370_);
if (v___x_5372_ == 0)
{
if (v___x_5371_ == 0)
{
lean_dec(v_ty_x3f_5368_);
return v_acc_5367_;
}
else
{
size_t v___x_5373_; size_t v___x_5374_; lean_object* v___x_5375_; 
v___x_5373_ = ((size_t)0ULL);
v___x_5374_ = lean_usize_of_nat(v___x_5370_);
v___x_5375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5368_, v_pats_5366_, v___x_5373_, v___x_5374_, v_acc_5367_);
return v___x_5375_;
}
}
else
{
size_t v___x_5376_; size_t v___x_5377_; lean_object* v___x_5378_; 
v___x_5376_ = ((size_t)0ULL);
v___x_5377_ = lean_usize_of_nat(v___x_5370_);
v___x_5378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5368_, v_pats_5366_, v___x_5376_, v___x_5377_, v_acc_5367_);
return v___x_5378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(lean_object* v_pat_5382_, lean_object* v_acc_5383_, lean_object* v_ty_x3f_5384_){
_start:
{
lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5385_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5382_);
v___x_5386_ = l_Lean_Syntax_isOfKind(v_pat_5382_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; uint8_t v___x_5388_; 
v___x_5387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5382_);
v___x_5388_ = l_Lean_Syntax_isOfKind(v_pat_5382_, v___x_5387_);
if (v___x_5388_ == 0)
{
lean_dec(v_ty_x3f_5384_);
lean_dec(v_pat_5382_);
return v_acc_5383_;
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; uint8_t v___x_5393_; 
v___x_5389_ = lean_unsigned_to_nat(1u);
v___x_5390_ = l_Lean_Syntax_getArg(v_pat_5382_, v___x_5389_);
v___x_5391_ = lean_unsigned_to_nat(2u);
v___x_5392_ = l_Lean_Syntax_getArg(v_pat_5382_, v___x_5391_);
lean_dec(v_pat_5382_);
v___x_5393_ = l_Lean_Syntax_isNone(v___x_5392_);
if (v___x_5393_ == 0)
{
uint8_t v___x_5394_; 
lean_dec(v_ty_x3f_5384_);
lean_inc(v___x_5392_);
v___x_5394_ = l_Lean_Syntax_matchesNull(v___x_5392_, v___x_5391_);
if (v___x_5394_ == 0)
{
lean_dec(v___x_5392_);
lean_dec(v___x_5390_);
return v_acc_5383_;
}
else
{
lean_object* v_ty_x3f_x27_5395_; lean_object* v___x_5396_; lean_object* v_pats_5397_; lean_object* v___x_5398_; 
v_ty_x3f_x27_5395_ = l_Lean_Syntax_getArg(v___x_5392_, v___x_5389_);
lean_dec(v___x_5392_);
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v_ty_x3f_x27_5395_);
v_pats_5397_ = l_Lean_Syntax_getArgs(v___x_5390_);
lean_dec(v___x_5390_);
v___x_5398_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5397_, v_acc_5383_, v___x_5396_);
lean_dec_ref(v_pats_5397_);
return v___x_5398_;
}
}
else
{
lean_object* v_pats_5399_; lean_object* v___x_5400_; 
lean_dec(v___x_5392_);
v_pats_5399_ = l_Lean_Syntax_getArgs(v___x_5390_);
lean_dec(v___x_5390_);
v___x_5400_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5399_, v_acc_5383_, v_ty_x3f_5384_);
lean_dec_ref(v_pats_5399_);
return v___x_5400_;
}
}
}
else
{
lean_object* v___x_5401_; lean_object* v_p_5402_; 
v___x_5401_ = lean_unsigned_to_nat(0u);
v_p_5402_ = l_Lean_Syntax_getArg(v_pat_5382_, v___x_5401_);
lean_dec(v_pat_5382_);
if (lean_obj_tag(v_ty_x3f_5384_) == 0)
{
lean_object* v___x_5403_; 
v___x_5403_ = lean_array_push(v_acc_5383_, v_p_5402_);
return v___x_5403_;
}
else
{
lean_object* v_val_5404_; lean_object* v___x_5405_; lean_object* v_ref_5406_; uint8_t v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v_val_5404_ = lean_ctor_get(v_ty_x3f_5384_, 0);
lean_inc(v_val_5404_);
lean_dec_ref_known(v_ty_x3f_5384_, 1);
v___x_5405_ = lean_box(0);
v_ref_5406_ = l_Lean_replaceRef(v_p_5402_, v___x_5405_);
v___x_5407_ = 0;
v___x_5408_ = l_Lean_SourceInfo_fromRef(v_ref_5406_, v___x_5407_);
lean_dec(v_ref_5406_);
v___x_5409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse___closed__9));
v___x_5410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__2));
lean_inc_n(v___x_5408_, 7);
v___x_5411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5408_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr4Nil__lean___lam__0___closed__1));
v___x_5413_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
v___x_5414_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__3));
v___x_5415_ = l_Lean_Syntax_node1(v___x_5408_, v___x_5414_, v_p_5402_);
v___x_5416_ = l_Lean_Syntax_node1(v___x_5408_, v___x_5413_, v___x_5415_);
v___x_5417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__3));
v___x_5418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___x_5408_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
v___x_5419_ = l_Lean_Syntax_node2(v___x_5408_, v___x_5414_, v___x_5418_, v_val_5404_);
v___x_5420_ = l_Lean_Syntax_node2(v___x_5408_, v___x_5412_, v___x_5416_, v___x_5419_);
v___x_5421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__4));
v___x_5422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5422_, 0, v___x_5408_);
lean_ctor_set(v___x_5422_, 1, v___x_5421_);
v___x_5423_ = l_Lean_Syntax_node3(v___x_5408_, v___x_5409_, v___x_5411_, v___x_5420_, v___x_5422_);
v___x_5424_ = lean_array_push(v_acc_5383_, v___x_5423_);
return v___x_5424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(lean_object* v_ty_x3f_5425_, lean_object* v_as_5426_, size_t v_i_5427_, size_t v_stop_5428_, lean_object* v_b_5429_){
_start:
{
uint8_t v___x_5430_; 
v___x_5430_ = lean_usize_dec_eq(v_i_5427_, v_stop_5428_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; lean_object* v___x_5432_; size_t v___x_5433_; size_t v___x_5434_; 
v___x_5431_ = lean_array_uget_borrowed(v_as_5426_, v_i_5427_);
lean_inc(v_ty_x3f_5425_);
lean_inc(v___x_5431_);
v___x_5432_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat(v___x_5431_, v_b_5429_, v_ty_x3f_5425_);
v___x_5433_ = ((size_t)1ULL);
v___x_5434_ = lean_usize_add(v_i_5427_, v___x_5433_);
v_i_5427_ = v___x_5434_;
v_b_5429_ = v___x_5432_;
goto _start;
}
else
{
lean_dec(v_ty_x3f_5425_);
return v_b_5429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1___boxed(lean_object* v_ty_x3f_5436_, lean_object* v_as_5437_, lean_object* v_i_5438_, lean_object* v_stop_5439_, lean_object* v_b_5440_){
_start:
{
size_t v_i_boxed_5441_; size_t v_stop_boxed_5442_; lean_object* v_res_5443_; 
v_i_boxed_5441_ = lean_unbox_usize(v_i_5438_);
lean_dec(v_i_5438_);
v_stop_boxed_5442_ = lean_unbox_usize(v_stop_5439_);
lean_dec(v_stop_5439_);
v_res_5443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_RCases_expandRIntroPats_spec__1(v_ty_x3f_5436_, v_as_5437_, v_i_boxed_5441_, v_stop_boxed_5442_, v_b_5440_);
lean_dec_ref(v_as_5437_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_expandRIntroPats___boxed(lean_object* v_pats_5444_, lean_object* v_acc_5445_, lean_object* v_ty_x3f_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Lean_Elab_Tactic_RCases_expandRIntroPats(v_pats_5444_, v_acc_5445_, v_ty_x3f_5446_);
lean_dec_ref(v_pats_5444_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg(){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5449_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg___boxed(lean_object* v___y_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed(lean_object* v_ref_5453_, lean_object* v_pats_5454_, lean_object* v_ty_x3f_5455_, lean_object* v_cont_5456_, lean_object* v_i_5457_, lean_object* v_g_5458_, lean_object* v_fs_5459_, lean_object* v_clears_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5453_, v_pats_5454_, v_ty_x3f_5455_, v_cont_5456_, v_i_5457_, v_g_5458_, v_fs_5459_, v_clears_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_i_5457_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_5470_ = _args[0];
lean_object* v_ref_5471_ = _args[1];
lean_object* v_pats_5472_ = _args[2];
lean_object* v_ty_x3f_5473_ = _args[3];
lean_object* v_cont_5474_ = _args[4];
lean_object* v_i_5475_ = _args[5];
lean_object* v_g_5476_ = _args[6];
lean_object* v_fs_5477_ = _args[7];
lean_object* v_clears_5478_ = _args[8];
lean_object* v_a_5479_ = _args[9];
lean_object* v_a_5480_ = _args[10];
lean_object* v_a_5481_ = _args[11];
lean_object* v_a_5482_ = _args[12];
lean_object* v_a_5483_ = _args[13];
lean_object* v_a_5484_ = _args[14];
lean_object* v_a_5485_ = _args[15];
lean_object* v_a_5486_ = _args[16];
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(v_00_u03b1_5470_, v_ref_5471_, v_pats_5472_, v_ty_x3f_5473_, v_cont_5474_, v_i_5475_, v_g_5476_, v_fs_5477_, v_clears_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec_ref(v_a_5482_);
lean_dec(v_a_5481_);
lean_dec_ref(v_a_5480_);
lean_dec(v_i_5475_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(lean_object* v_g_5488_, lean_object* v_fs_5489_, lean_object* v_clears_5490_, lean_object* v_ref_5491_, lean_object* v_pats_5492_, lean_object* v_ty_x3f_5493_, lean_object* v_a_5494_, lean_object* v_cont_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5503_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_5488_);
v___x_5504_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___boxed), 17, 10);
lean_closure_set(v___x_5504_, 0, lean_box(0));
lean_closure_set(v___x_5504_, 1, v_ref_5491_);
lean_closure_set(v___x_5504_, 2, v_pats_5492_);
lean_closure_set(v___x_5504_, 3, v_ty_x3f_5493_);
lean_closure_set(v___x_5504_, 4, v_cont_5495_);
lean_closure_set(v___x_5504_, 5, v___x_5503_);
lean_closure_set(v___x_5504_, 6, v_g_5488_);
lean_closure_set(v___x_5504_, 7, v_fs_5489_);
lean_closure_set(v___x_5504_, 8, v_clears_5490_);
lean_closure_set(v___x_5504_, 9, v_a_5494_);
v___x_5505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore_spec__7___redArg(v_g_5488_, v___x_5504_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(lean_object* v_g_5506_, lean_object* v_fs_5507_, lean_object* v_clears_5508_, lean_object* v_a_5509_, lean_object* v_ref_5510_, lean_object* v_pat_5511_, lean_object* v_ty_x3f_5512_, lean_object* v_cont_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_){
_start:
{
lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___x_5533_; uint8_t v___x_5534_; 
v___x_5533_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1Nil__lean___lam__0___closed__1));
lean_inc(v_pat_5511_);
v___x_5534_ = l_Lean_Syntax_isOfKind(v_pat_5511_, v___x_5533_);
if (v___x_5534_ == 0)
{
lean_object* v___x_5535_; uint8_t v___x_5536_; 
lean_dec(v_ref_5510_);
v___x_5535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_expandRIntroPat___closed__1));
lean_inc(v_pat_5511_);
v___x_5536_ = l_Lean_Syntax_isOfKind(v_pat_5511_, v___x_5535_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5537_; 
lean_dec_ref(v_cont_5513_);
lean_dec(v_ty_x3f_5512_);
lean_dec(v_pat_5511_);
lean_dec(v_a_5509_);
lean_dec_ref(v_clears_5508_);
lean_dec(v_fs_5507_);
lean_dec(v_g_5506_);
v___x_5537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5537_;
}
else
{
lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v_ty_x3f_x27_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___x_5552_; lean_object* v___x_5553_; uint8_t v___x_5554_; 
v___x_5538_ = lean_unsigned_to_nat(1u);
v___x_5539_ = l_Lean_Syntax_getArg(v_pat_5511_, v___x_5538_);
v___x_5552_ = lean_unsigned_to_nat(2u);
v___x_5553_ = l_Lean_Syntax_getArg(v_pat_5511_, v___x_5552_);
v___x_5554_ = l_Lean_Syntax_isNone(v___x_5553_);
if (v___x_5554_ == 0)
{
uint8_t v___x_5555_; 
lean_inc(v___x_5553_);
v___x_5555_ = l_Lean_Syntax_matchesNull(v___x_5553_, v___x_5552_);
if (v___x_5555_ == 0)
{
lean_object* v___x_5556_; 
lean_dec(v___x_5553_);
lean_dec(v___x_5539_);
lean_dec_ref(v_cont_5513_);
lean_dec(v_ty_x3f_5512_);
lean_dec(v_pat_5511_);
lean_dec(v_a_5509_);
lean_dec_ref(v_clears_5508_);
lean_dec(v_fs_5507_);
lean_dec(v_g_5506_);
v___x_5556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5556_;
}
else
{
lean_object* v_ty_x3f_x27_5557_; lean_object* v___x_5558_; 
v_ty_x3f_x27_5557_ = l_Lean_Syntax_getArg(v___x_5553_, v___x_5538_);
lean_dec(v___x_5553_);
v___x_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5558_, 0, v_ty_x3f_x27_5557_);
v_ty_x3f_x27_5541_ = v___x_5558_;
v___y_5542_ = v_a_5514_;
v___y_5543_ = v_a_5515_;
v___y_5544_ = v_a_5516_;
v___y_5545_ = v_a_5517_;
v___y_5546_ = v_a_5518_;
v___y_5547_ = v_a_5519_;
goto v___jp_5540_;
}
}
else
{
lean_object* v___x_5559_; 
lean_dec(v___x_5553_);
v___x_5559_ = lean_box(0);
v_ty_x3f_x27_5541_ = v___x_5559_;
v___y_5542_ = v_a_5514_;
v___y_5543_ = v_a_5515_;
v___y_5544_ = v_a_5516_;
v___y_5545_ = v_a_5517_;
v___y_5546_ = v_a_5518_;
v___y_5547_ = v_a_5519_;
goto v___jp_5540_;
}
v___jp_5540_:
{
lean_object* v_pats_5548_; lean_object* v___x_5549_; uint8_t v___x_5550_; 
v_pats_5548_ = l_Lean_Syntax_getArgs(v___x_5539_);
lean_dec(v___x_5539_);
v___x_5549_ = lean_array_get_size(v_pats_5548_);
v___x_5550_ = lean_nat_dec_eq(v___x_5549_, v___x_5538_);
if (v___x_5550_ == 0)
{
lean_object* v___x_5551_; 
lean_dec(v_pat_5511_);
v___x_5551_ = lean_box(0);
v___y_5522_ = v___y_5545_;
v___y_5523_ = v___y_5542_;
v___y_5524_ = v___y_5544_;
v___y_5525_ = v___y_5546_;
v___y_5526_ = v___y_5543_;
v___y_5527_ = v___y_5547_;
v___y_5528_ = v_ty_x3f_x27_5541_;
v___y_5529_ = v_pats_5548_;
v___y_5530_ = v___x_5551_;
goto v___jp_5521_;
}
else
{
v___y_5522_ = v___y_5545_;
v___y_5523_ = v___y_5542_;
v___y_5524_ = v___y_5544_;
v___y_5525_ = v___y_5546_;
v___y_5526_ = v___y_5543_;
v___y_5527_ = v___y_5547_;
v___y_5528_ = v_ty_x3f_x27_5541_;
v___y_5529_ = v_pats_5548_;
v___y_5530_ = v_pat_5511_;
goto v___jp_5521_;
}
}
}
}
else
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v___x_5560_ = lean_unsigned_to_nat(0u);
v___x_5561_ = l_Lean_Syntax_getArg(v_pat_5511_, v___x_5560_);
lean_dec(v_pat_5511_);
v___x_5562_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v___x_5561_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_object* v_a_5563_; lean_object* v___x_5564_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5601_; lean_object* v_ref_5605_; 
v_a_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_a_5563_);
lean_dec_ref_known(v___x_5562_, 1);
v___x_5564_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_ref_5510_, v_a_5563_, v_ty_x3f_5512_);
lean_dec(v_ty_x3f_5512_);
v_ref_5605_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_ref_5605_);
v___y_5601_ = v_ref_5605_;
goto v___jp_5600_;
v___jp_5565_:
{
lean_object* v_fileName_5568_; lean_object* v_fileMap_5569_; lean_object* v_options_5570_; lean_object* v_currRecDepth_5571_; lean_object* v_maxRecDepth_5572_; lean_object* v_ref_5573_; lean_object* v_currNamespace_5574_; lean_object* v_openDecls_5575_; lean_object* v_initHeartbeats_5576_; lean_object* v_maxHeartbeats_5577_; lean_object* v_quotContext_5578_; lean_object* v_currMacroScope_5579_; uint8_t v_diag_5580_; lean_object* v_cancelTk_x3f_5581_; uint8_t v_suppressElabErrors_5582_; lean_object* v_inheritedTraceOptions_5583_; lean_object* v_ref_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; 
v_fileName_5568_ = lean_ctor_get(v_a_5518_, 0);
v_fileMap_5569_ = lean_ctor_get(v_a_5518_, 1);
v_options_5570_ = lean_ctor_get(v_a_5518_, 2);
v_currRecDepth_5571_ = lean_ctor_get(v_a_5518_, 3);
v_maxRecDepth_5572_ = lean_ctor_get(v_a_5518_, 4);
v_ref_5573_ = lean_ctor_get(v_a_5518_, 5);
v_currNamespace_5574_ = lean_ctor_get(v_a_5518_, 6);
v_openDecls_5575_ = lean_ctor_get(v_a_5518_, 7);
v_initHeartbeats_5576_ = lean_ctor_get(v_a_5518_, 8);
v_maxHeartbeats_5577_ = lean_ctor_get(v_a_5518_, 9);
v_quotContext_5578_ = lean_ctor_get(v_a_5518_, 10);
v_currMacroScope_5579_ = lean_ctor_get(v_a_5518_, 11);
v_diag_5580_ = lean_ctor_get_uint8(v_a_5518_, sizeof(void*)*14);
v_cancelTk_x3f_5581_ = lean_ctor_get(v_a_5518_, 12);
v_suppressElabErrors_5582_ = lean_ctor_get_uint8(v_a_5518_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5583_ = lean_ctor_get(v_a_5518_, 13);
v_ref_5584_ = l_Lean_replaceRef(v___y_5566_, v_ref_5573_);
lean_dec(v___y_5566_);
lean_inc_ref(v_inheritedTraceOptions_5583_);
lean_inc(v_cancelTk_x3f_5581_);
lean_inc(v_currMacroScope_5579_);
lean_inc(v_quotContext_5578_);
lean_inc(v_maxHeartbeats_5577_);
lean_inc(v_initHeartbeats_5576_);
lean_inc(v_openDecls_5575_);
lean_inc(v_currNamespace_5574_);
lean_inc(v_maxRecDepth_5572_);
lean_inc(v_currRecDepth_5571_);
lean_inc_ref(v_options_5570_);
lean_inc_ref(v_fileMap_5569_);
lean_inc_ref(v_fileName_5568_);
v___x_5585_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5585_, 0, v_fileName_5568_);
lean_ctor_set(v___x_5585_, 1, v_fileMap_5569_);
lean_ctor_set(v___x_5585_, 2, v_options_5570_);
lean_ctor_set(v___x_5585_, 3, v_currRecDepth_5571_);
lean_ctor_set(v___x_5585_, 4, v_maxRecDepth_5572_);
lean_ctor_set(v___x_5585_, 5, v_ref_5584_);
lean_ctor_set(v___x_5585_, 6, v_currNamespace_5574_);
lean_ctor_set(v___x_5585_, 7, v_openDecls_5575_);
lean_ctor_set(v___x_5585_, 8, v_initHeartbeats_5576_);
lean_ctor_set(v___x_5585_, 9, v_maxHeartbeats_5577_);
lean_ctor_set(v___x_5585_, 10, v_quotContext_5578_);
lean_ctor_set(v___x_5585_, 11, v_currMacroScope_5579_);
lean_ctor_set(v___x_5585_, 12, v_cancelTk_x3f_5581_);
lean_ctor_set(v___x_5585_, 13, v_inheritedTraceOptions_5583_);
lean_ctor_set_uint8(v___x_5585_, sizeof(void*)*14, v_diag_5580_);
lean_ctor_set_uint8(v___x_5585_, sizeof(void*)*14 + 1, v_suppressElabErrors_5582_);
v___x_5586_ = l_Lean_MVarId_intro(v_g_5506_, v___y_5567_, v_a_5516_, v_a_5517_, v___x_5585_, v_a_5519_);
lean_dec_ref_known(v___x_5585_, 14);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v_a_5587_; lean_object* v_fst_5588_; lean_object* v_snd_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v_a_5587_);
lean_dec_ref_known(v___x_5586_, 1);
v_fst_5588_ = lean_ctor_get(v_a_5587_, 0);
lean_inc(v_fst_5588_);
v_snd_5589_ = lean_ctor_get(v_a_5587_, 1);
lean_inc(v_snd_5589_);
lean_dec(v_a_5587_);
v___x_5590_ = l_Lean_Expr_fvar___override(v_fst_5588_);
v___x_5591_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rcasesCore___redArg(v_snd_5589_, v_fs_5507_, v_clears_5508_, v___x_5590_, v_a_5509_, v___x_5564_, v_cont_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_);
lean_dec_ref(v___x_5590_);
return v___x_5591_;
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec_ref(v___x_5564_);
lean_dec_ref(v_cont_5513_);
lean_dec(v_a_5509_);
lean_dec_ref(v_clears_5508_);
lean_dec(v_fs_5507_);
v_a_5592_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5586_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5586_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
v___jp_5600_:
{
lean_object* v___x_5602_; 
v___x_5602_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_name_x3f(v___x_5564_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_object* v___x_5603_; 
v___x_5603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
v___y_5566_ = v___y_5601_;
v___y_5567_ = v___x_5603_;
goto v___jp_5565_;
}
else
{
lean_object* v_val_5604_; 
v_val_5604_ = lean_ctor_get(v___x_5602_, 0);
lean_inc(v_val_5604_);
lean_dec_ref_known(v___x_5602_, 1);
v___y_5566_ = v___y_5601_;
v___y_5567_ = v_val_5604_;
goto v___jp_5565_;
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
lean_dec_ref(v_cont_5513_);
lean_dec(v_ty_x3f_5512_);
lean_dec(v_ref_5510_);
lean_dec(v_a_5509_);
lean_dec_ref(v_clears_5508_);
lean_dec(v_fs_5507_);
lean_dec(v_g_5506_);
v_a_5606_ = lean_ctor_get(v___x_5562_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5562_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5562_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
v___jp_5521_:
{
if (lean_obj_tag(v___y_5528_) == 0)
{
lean_object* v___x_5531_; 
v___x_5531_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5506_, v_fs_5507_, v_clears_5508_, v___y_5530_, v___y_5529_, v_ty_x3f_5512_, v_a_5509_, v_cont_5513_, v___y_5523_, v___y_5526_, v___y_5524_, v___y_5522_, v___y_5525_, v___y_5527_);
return v___x_5531_;
}
else
{
lean_object* v___x_5532_; 
lean_dec(v_ty_x3f_5512_);
v___x_5532_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5506_, v_fs_5507_, v_clears_5508_, v___y_5530_, v___y_5529_, v___y_5528_, v_a_5509_, v_cont_5513_, v___y_5523_, v___y_5526_, v___y_5524_, v___y_5522_, v___y_5525_, v___y_5527_);
return v___x_5532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(lean_object* v_ref_5614_, lean_object* v_pats_5615_, lean_object* v_ty_x3f_5616_, lean_object* v_cont_5617_, lean_object* v_i_5618_, lean_object* v_g_5619_, lean_object* v_fs_5620_, lean_object* v_clears_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v___x_5630_; uint8_t v___x_5631_; 
v___x_5630_ = lean_array_get_size(v_pats_5615_);
v___x_5631_ = lean_nat_dec_lt(v_i_5618_, v___x_5630_);
if (v___x_5631_ == 0)
{
lean_object* v___x_5632_; 
lean_dec(v_ty_x3f_5616_);
lean_dec_ref(v_pats_5615_);
lean_dec(v_ref_5614_);
lean_inc(v_a_5628_);
lean_inc_ref(v_a_5627_);
lean_inc(v_a_5626_);
lean_inc_ref(v_a_5625_);
lean_inc(v_a_5624_);
lean_inc_ref(v_a_5623_);
v___x_5632_ = lean_apply_11(v_cont_5617_, v_g_5619_, v_fs_5620_, v_clears_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, lean_box(0));
return v___x_5632_;
}
else
{
lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v___x_5633_ = lean_array_fget(v_pats_5615_, v_i_5618_);
v___x_5634_ = lean_unsigned_to_nat(1u);
v___x_5635_ = lean_nat_add(v_i_5618_, v___x_5634_);
lean_inc(v_ty_x3f_5616_);
lean_inc(v_ref_5614_);
v___x_5636_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg___boxed), 16, 5);
lean_closure_set(v___x_5636_, 0, v_ref_5614_);
lean_closure_set(v___x_5636_, 1, v_pats_5615_);
lean_closure_set(v___x_5636_, 2, v_ty_x3f_5616_);
lean_closure_set(v___x_5636_, 3, v_cont_5617_);
lean_closure_set(v___x_5636_, 4, v___x_5635_);
v___x_5637_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5619_, v_fs_5620_, v_clears_5621_, v_a_5622_, v_ref_5614_, v___x_5633_, v_ty_x3f_5616_, v___x_5636_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_);
return v___x_5637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop(lean_object* v_00_u03b1_5638_, lean_object* v_ref_5639_, lean_object* v_pats_5640_, lean_object* v_ty_x3f_5641_, lean_object* v_cont_5642_, lean_object* v_i_5643_, lean_object* v_g_5644_, lean_object* v_fs_5645_, lean_object* v_clears_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v___x_5655_; 
v___x_5655_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue_loop___redArg(v_ref_5639_, v_pats_5640_, v_ty_x3f_5641_, v_cont_5642_, v_i_5643_, v_g_5644_, v_fs_5645_, v_clears_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg___boxed(lean_object* v_g_5656_, lean_object* v_fs_5657_, lean_object* v_clears_5658_, lean_object* v_ref_5659_, lean_object* v_pats_5660_, lean_object* v_ty_x3f_5661_, lean_object* v_a_5662_, lean_object* v_cont_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_){
_start:
{
lean_object* v_res_5671_; 
v_res_5671_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5656_, v_fs_5657_, v_clears_5658_, v_ref_5659_, v_pats_5660_, v_ty_x3f_5661_, v_a_5662_, v_cont_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_);
lean_dec(v_a_5669_);
lean_dec_ref(v_a_5668_);
lean_dec(v_a_5667_);
lean_dec_ref(v_a_5666_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg___boxed(lean_object* v_g_5672_, lean_object* v_fs_5673_, lean_object* v_clears_5674_, lean_object* v_a_5675_, lean_object* v_ref_5676_, lean_object* v_pat_5677_, lean_object* v_ty_x3f_5678_, lean_object* v_cont_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5672_, v_fs_5673_, v_clears_5674_, v_a_5675_, v_ref_5676_, v_pat_5677_, v_ty_x3f_5678_, v_cont_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_);
lean_dec(v_a_5685_);
lean_dec_ref(v_a_5684_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(lean_object* v_00_u03b1_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_){
_start:
{
lean_object* v___x_5696_; 
v___x_5696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___redArg();
return v___x_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1___boxed(lean_object* v_00_u03b1_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore_spec__1(v_00_u03b1_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(lean_object* v_00_u03b1_5706_, lean_object* v_g_5707_, lean_object* v_fs_5708_, lean_object* v_clears_5709_, lean_object* v_a_5710_, lean_object* v_ref_5711_, lean_object* v_pat_5712_, lean_object* v_ty_x3f_5713_, lean_object* v_cont_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_){
_start:
{
lean_object* v___x_5722_; 
v___x_5722_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___redArg(v_g_5707_, v_fs_5708_, v_clears_5709_, v_a_5710_, v_ref_5711_, v_pat_5712_, v_ty_x3f_5713_, v_cont_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_);
return v___x_5722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore___boxed(lean_object* v_00_u03b1_5723_, lean_object* v_g_5724_, lean_object* v_fs_5725_, lean_object* v_clears_5726_, lean_object* v_a_5727_, lean_object* v_ref_5728_, lean_object* v_pat_5729_, lean_object* v_ty_x3f_5730_, lean_object* v_cont_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroCore(v_00_u03b1_5723_, v_g_5724_, v_fs_5725_, v_clears_5726_, v_a_5727_, v_ref_5728_, v_pat_5729_, v_ty_x3f_5730_, v_cont_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(lean_object* v_00_u03b1_5740_, lean_object* v_g_5741_, lean_object* v_fs_5742_, lean_object* v_clears_5743_, lean_object* v_ref_5744_, lean_object* v_pats_5745_, lean_object* v_ty_x3f_5746_, lean_object* v_a_5747_, lean_object* v_cont_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5741_, v_fs_5742_, v_clears_5743_, v_ref_5744_, v_pats_5745_, v_ty_x3f_5746_, v_a_5747_, v_cont_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___boxed(lean_object* v_00_u03b1_5757_, lean_object* v_g_5758_, lean_object* v_fs_5759_, lean_object* v_clears_5760_, lean_object* v_ref_5761_, lean_object* v_pats_5762_, lean_object* v_ty_x3f_5763_, lean_object* v_a_5764_, lean_object* v_cont_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue(v_00_u03b1_5757_, v_g_5758_, v_fs_5759_, v_clears_5760_, v_ref_5761_, v_pats_5762_, v_ty_x3f_5763_, v_a_5764_, v_cont_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
lean_dec(v_a_5771_);
lean_dec_ref(v_a_5770_);
lean_dec(v_a_5769_);
lean_dec_ref(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0(lean_object* v_g_5774_, lean_object* v___x_5775_, lean_object* v___x_5776_, lean_object* v___x_5777_, lean_object* v_pats_5778_, lean_object* v_ty_x3f_5779_, lean_object* v___x_5780_, lean_object* v___x_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_rintroContinue___redArg(v_g_5774_, v___x_5775_, v___x_5776_, v___x_5777_, v_pats_5778_, v_ty_x3f_5779_, v___x_5780_, v___x_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5798_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5792_ = v___x_5789_;
v_isShared_5793_ = v_isSharedCheck_5798_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5789_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5798_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5794_; lean_object* v___x_5796_; 
v___x_5794_ = lean_array_to_list(v_a_5790_);
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 0, v___x_5794_);
v___x_5796_ = v___x_5792_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
v_a_5799_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5789_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5789_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed(lean_object* v_g_5807_, lean_object* v___x_5808_, lean_object* v___x_5809_, lean_object* v___x_5810_, lean_object* v_pats_5811_, lean_object* v_ty_x3f_5812_, lean_object* v___x_5813_, lean_object* v___x_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Lean_Elab_Tactic_RCases_rintro___lam__0(v_g_5807_, v___x_5808_, v___x_5809_, v___x_5810_, v_pats_5811_, v_ty_x3f_5812_, v___x_5813_, v___x_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
return v_res_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro(lean_object* v_pats_5823_, lean_object* v_ty_x3f_5824_, lean_object* v_g_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_, lean_object* v_a_5830_, lean_object* v_a_5831_){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___f_5837_; uint8_t v___x_5838_; lean_object* v___x_5839_; 
v___x_5833_ = lean_box(0);
v___x_5834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__0));
v___x_5835_ = lean_box(0);
v___x_5836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone___lam__0___closed__1));
v___f_5837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_RCases_rintro___lam__0___boxed), 15, 8);
lean_closure_set(v___f_5837_, 0, v_g_5825_);
lean_closure_set(v___f_5837_, 1, v___x_5833_);
lean_closure_set(v___f_5837_, 2, v___x_5834_);
lean_closure_set(v___f_5837_, 3, v___x_5835_);
lean_closure_set(v___f_5837_, 4, v_pats_5823_);
lean_closure_set(v___f_5837_, 5, v_ty_x3f_5824_);
lean_closure_set(v___f_5837_, 6, v___x_5834_);
lean_closure_set(v___f_5837_, 7, v___x_5836_);
v___x_5838_ = 1;
v___x_5839_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___f_5837_, v___x_5838_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_RCases_rintro___boxed(lean_object* v_pats_5840_, lean_object* v_ty_x3f_5841_, lean_object* v_g_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_){
_start:
{
lean_object* v_res_5850_; 
v_res_5850_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_5840_, v_ty_x3f_5841_, v_g_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_);
lean_dec(v_a_5848_);
lean_dec_ref(v_a_5847_);
lean_dec(v_a_5846_);
lean_dec_ref(v_a_5845_);
lean_dec(v_a_5844_);
lean_dec_ref(v_a_5843_);
return v_res_5850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg(){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse_spec__0___redArg___closed__0);
v___x_5853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5852_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg___boxed(lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(lean_object* v_00_u03b1_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_){
_start:
{
lean_object* v___x_5866_; 
v___x_5866_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___boxed(lean_object* v_00_u03b1_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0(v_00_u03b1_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(lean_object* v_x_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_){
_start:
{
lean_object* v___x_5888_; 
lean_inc(v___y_5882_);
lean_inc_ref(v___y_5881_);
lean_inc(v___y_5880_);
lean_inc_ref(v___y_5879_);
v___x_5888_ = lean_apply_9(v_x_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, lean_box(0));
return v___x_5888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed(lean_object* v_x_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
lean_object* v_res_5899_; 
v_res_5899_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0(v_x_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
lean_dec(v___y_5893_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
return v_res_5899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(lean_object* v_mvarId_5900_, lean_object* v_x_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_){
_start:
{
lean_object* v___f_5911_; lean_object* v___x_5912_; 
lean_inc(v___y_5905_);
lean_inc_ref(v___y_5904_);
lean_inc(v___y_5903_);
lean_inc_ref(v___y_5902_);
v___f_5911_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_5911_, 0, v_x_5901_);
lean_closure_set(v___f_5911_, 1, v___y_5902_);
lean_closure_set(v___f_5911_, 2, v___y_5903_);
lean_closure_set(v___f_5911_, 3, v___y_5904_);
lean_closure_set(v___f_5911_, 4, v___y_5905_);
v___x_5912_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5900_, v___f_5911_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_);
if (lean_obj_tag(v___x_5912_) == 0)
{
return v___x_5912_;
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5912_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5912_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg___boxed(lean_object* v_mvarId_5921_, lean_object* v_x_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_){
_start:
{
lean_object* v_res_5932_; 
v_res_5932_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5921_, v_x_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
lean_dec(v___y_5930_);
lean_dec_ref(v___y_5929_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
return v_res_5932_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(lean_object* v_00_u03b1_5933_, lean_object* v_mvarId_5934_, lean_object* v_x_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_){
_start:
{
lean_object* v___x_5945_; 
v___x_5945_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_mvarId_5934_, v_x_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_, v___y_5943_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___boxed(lean_object* v_00_u03b1_5946_, lean_object* v_mvarId_5947_, lean_object* v_x_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_){
_start:
{
lean_object* v_res_5958_; 
v_res_5958_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2(v_00_u03b1_5946_, v_mvarId_5947_, v_x_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_);
lean_dec(v___y_5956_);
lean_dec_ref(v___y_5955_);
lean_dec(v___y_5954_);
lean_dec_ref(v___y_5953_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
return v_res_5958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(lean_object* v_a_5959_, lean_object* v_pat_5960_, lean_object* v_a_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_){
_start:
{
lean_object* v___x_5971_; 
v___x_5971_ = l_Lean_Elab_Tactic_RCases_rcases(v_a_5959_, v_pat_5960_, v_a_5961_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5973_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
v___x_5973_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_5972_, v___y_5963_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
return v___x_5973_;
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
v_a_5974_ = lean_ctor_get(v___x_5971_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5971_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5971_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5971_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5977_ == 0)
{
v___x_5979_ = v___x_5976_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
return v___x_5979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed(lean_object* v_a_5982_, lean_object* v_pat_5983_, lean_object* v_a_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_){
_start:
{
lean_object* v_res_5994_; 
v_res_5994_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0(v_a_5982_, v_pat_5983_, v_a_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
lean_dec(v___y_5992_);
lean_dec_ref(v___y_5991_);
lean_dec(v___y_5990_);
lean_dec_ref(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec(v___y_5986_);
lean_dec_ref(v___y_5985_);
return v_res_5994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(size_t v_sz_5995_, size_t v_i_5996_, lean_object* v_bs_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_){
_start:
{
uint8_t v___x_6002_; 
v___x_6002_ = lean_usize_dec_lt(v_i_5996_, v_sz_5995_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; 
v___x_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6003_, 0, v_bs_5997_);
return v___x_6003_;
}
else
{
lean_object* v_v_6004_; lean_object* v___x_6005_; 
v_v_6004_ = lean_array_uget_borrowed(v_bs_5997_, v_i_5996_);
lean_inc(v_v_6004_);
v___x_6005_ = l_Lean_Elab_Tactic_mkTargetView___redArg(v_v_6004_, v___y_5998_, v___y_5999_, v___y_6000_);
if (lean_obj_tag(v___x_6005_) == 0)
{
lean_object* v_a_6006_; lean_object* v_hIdent_x3f_6007_; lean_object* v_term_6008_; lean_object* v___x_6010_; uint8_t v_isShared_6011_; uint8_t v_isSharedCheck_6021_; 
v_a_6006_ = lean_ctor_get(v___x_6005_, 0);
lean_inc(v_a_6006_);
lean_dec_ref_known(v___x_6005_, 1);
v_hIdent_x3f_6007_ = lean_ctor_get(v_a_6006_, 0);
v_term_6008_ = lean_ctor_get(v_a_6006_, 1);
v_isSharedCheck_6021_ = !lean_is_exclusive(v_a_6006_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_6010_ = v_a_6006_;
v_isShared_6011_ = v_isSharedCheck_6021_;
goto v_resetjp_6009_;
}
else
{
lean_inc(v_term_6008_);
lean_inc(v_hIdent_x3f_6007_);
lean_dec(v_a_6006_);
v___x_6010_ = lean_box(0);
v_isShared_6011_ = v_isSharedCheck_6021_;
goto v_resetjp_6009_;
}
v_resetjp_6009_:
{
lean_object* v___x_6012_; lean_object* v_bs_x27_6013_; lean_object* v___x_6015_; 
v___x_6012_ = lean_unsigned_to_nat(0u);
v_bs_x27_6013_ = lean_array_uset(v_bs_5997_, v_i_5996_, v___x_6012_);
if (v_isShared_6011_ == 0)
{
v___x_6015_ = v___x_6010_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_hIdent_x3f_6007_);
lean_ctor_set(v_reuseFailAlloc_6020_, 1, v_term_6008_);
v___x_6015_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
size_t v___x_6016_; size_t v___x_6017_; lean_object* v___x_6018_; 
v___x_6016_ = ((size_t)1ULL);
v___x_6017_ = lean_usize_add(v_i_5996_, v___x_6016_);
v___x_6018_ = lean_array_uset(v_bs_x27_6013_, v_i_5996_, v___x_6015_);
v_i_5996_ = v___x_6017_;
v_bs_5997_ = v___x_6018_;
goto _start;
}
}
}
else
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
lean_dec_ref(v_bs_5997_);
v_a_6022_ = lean_ctor_get(v___x_6005_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_6005_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_6005_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_6005_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
return v___x_6027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg___boxed(lean_object* v_sz_6030_, lean_object* v_i_6031_, lean_object* v_bs_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
size_t v_sz_boxed_6037_; size_t v_i_boxed_6038_; lean_object* v_res_6039_; 
v_sz_boxed_6037_ = lean_unbox_usize(v_sz_6030_);
lean_dec(v_sz_6030_);
v_i_boxed_6038_ = lean_unbox_usize(v_i_6031_);
lean_dec(v_i_6031_);
v_res_6039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_boxed_6037_, v_i_boxed_6038_, v_bs_6032_, v___y_6033_, v___y_6034_, v___y_6035_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec_ref(v___y_6033_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(lean_object* v_stx_6046_, lean_object* v_a_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_){
_start:
{
lean_object* v___y_6057_; lean_object* v_pat_6058_; lean_object* v___y_6059_; lean_object* v___y_6060_; lean_object* v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6064_; lean_object* v___y_6065_; lean_object* v___y_6066_; lean_object* v___x_6092_; uint8_t v___x_6093_; 
v___x_6092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
lean_inc(v_stx_6046_);
v___x_6093_ = l_Lean_Syntax_isOfKind(v_stx_6046_, v___x_6092_);
if (v___x_6093_ == 0)
{
lean_object* v___x_6094_; 
lean_dec(v_stx_6046_);
v___x_6094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6094_;
}
else
{
lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; uint8_t v___x_6099_; 
v___x_6095_ = lean_unsigned_to_nat(1u);
v___x_6096_ = l_Lean_Syntax_getArg(v_stx_6046_, v___x_6095_);
v___x_6097_ = lean_unsigned_to_nat(2u);
v___x_6098_ = l_Lean_Syntax_getArg(v_stx_6046_, v___x_6097_);
v___x_6099_ = l_Lean_Syntax_isNone(v___x_6098_);
if (v___x_6099_ == 0)
{
uint8_t v___x_6100_; 
lean_dec(v_stx_6046_);
lean_inc(v___x_6098_);
v___x_6100_ = l_Lean_Syntax_matchesNull(v___x_6098_, v___x_6097_);
if (v___x_6100_ == 0)
{
lean_object* v___x_6101_; 
lean_dec(v___x_6098_);
lean_dec(v___x_6096_);
v___x_6101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6101_;
}
else
{
lean_object* v_pat_x3f_6102_; lean_object* v___x_6103_; 
v_pat_x3f_6102_ = l_Lean_Syntax_getArg(v___x_6098_, v___x_6095_);
lean_dec(v___x_6098_);
v___x_6103_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_pat_x3f_6102_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v_a_6104_; lean_object* v_tgts_6105_; 
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
lean_inc(v_a_6104_);
lean_dec_ref_known(v___x_6103_, 1);
v_tgts_6105_ = l_Lean_Syntax_getArgs(v___x_6096_);
lean_dec(v___x_6096_);
v___y_6057_ = v_tgts_6105_;
v_pat_6058_ = v_a_6104_;
v___y_6059_ = v_a_6047_;
v___y_6060_ = v_a_6048_;
v___y_6061_ = v_a_6049_;
v___y_6062_ = v_a_6050_;
v___y_6063_ = v_a_6051_;
v___y_6064_ = v_a_6052_;
v___y_6065_ = v_a_6053_;
v___y_6066_ = v_a_6054_;
goto v___jp_6056_;
}
else
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6113_; 
lean_dec(v___x_6096_);
v_a_6106_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6113_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6113_ == 0)
{
v___x_6108_ = v___x_6103_;
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6103_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6111_; 
if (v_isShared_6109_ == 0)
{
v___x_6111_ = v___x_6108_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6106_);
v___x_6111_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
return v___x_6111_;
}
}
}
}
}
else
{
lean_object* v___x_6114_; lean_object* v_tk_6115_; lean_object* v_tgts_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
lean_dec(v___x_6098_);
v___x_6114_ = lean_unsigned_to_nat(0u);
v_tk_6115_ = l_Lean_Syntax_getArg(v_stx_6046_, v___x_6114_);
lean_dec(v_stx_6046_);
v_tgts_6116_ = l_Lean_Syntax_getArgs(v___x_6096_);
lean_dec(v___x_6096_);
v___x_6117_ = lean_box(0);
v___x_6118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6118_, 0, v_tk_6115_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___y_6057_ = v_tgts_6116_;
v_pat_6058_ = v___x_6118_;
v___y_6059_ = v_a_6047_;
v___y_6060_ = v_a_6048_;
v___y_6061_ = v_a_6049_;
v___y_6062_ = v_a_6050_;
v___y_6063_ = v_a_6051_;
v___y_6064_ = v_a_6052_;
v___y_6065_ = v_a_6053_;
v___y_6066_ = v_a_6054_;
goto v___jp_6056_;
}
}
v___jp_6056_:
{
lean_object* v___x_6067_; size_t v_sz_6068_; size_t v___x_6069_; lean_object* v___x_6070_; 
v___x_6067_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6057_);
lean_dec_ref(v___y_6057_);
v_sz_6068_ = lean_array_size(v___x_6067_);
v___x_6069_ = ((size_t)0ULL);
v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6068_, v___x_6069_, v___x_6067_, v___y_6063_, v___y_6065_, v___y_6066_);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v_a_6071_; lean_object* v___x_6072_; 
v_a_6071_ = lean_ctor_get(v___x_6070_, 0);
lean_inc(v_a_6071_);
lean_dec_ref_known(v___x_6070_, 1);
v___x_6072_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6060_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
if (lean_obj_tag(v___x_6072_) == 0)
{
lean_object* v_a_6073_; lean_object* v___f_6074_; lean_object* v___x_6075_; 
v_a_6073_ = lean_ctor_get(v___x_6072_, 0);
lean_inc_n(v_a_6073_, 2);
lean_dec_ref_known(v___x_6072_, 1);
v___f_6074_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6074_, 0, v_a_6071_);
lean_closure_set(v___f_6074_, 1, v_pat_6058_);
lean_closure_set(v___f_6074_, 2, v_a_6073_);
v___x_6075_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6073_, v___f_6074_, v___y_6059_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
return v___x_6075_;
}
else
{
lean_object* v_a_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6083_; 
lean_dec(v_a_6071_);
lean_dec_ref(v_pat_6058_);
v_a_6076_ = lean_ctor_get(v___x_6072_, 0);
v_isSharedCheck_6083_ = !lean_is_exclusive(v___x_6072_);
if (v_isSharedCheck_6083_ == 0)
{
v___x_6078_ = v___x_6072_;
v_isShared_6079_ = v_isSharedCheck_6083_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_a_6076_);
lean_dec(v___x_6072_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6083_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6081_; 
if (v_isShared_6079_ == 0)
{
v___x_6081_ = v___x_6078_;
goto v_reusejp_6080_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_a_6076_);
v___x_6081_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6080_;
}
v_reusejp_6080_:
{
return v___x_6081_;
}
}
}
}
else
{
lean_object* v_a_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6091_; 
lean_dec_ref(v_pat_6058_);
v_a_6084_ = lean_ctor_get(v___x_6070_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6070_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6086_ = v___x_6070_;
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_a_6084_);
lean_dec(v___x_6070_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6089_; 
if (v_isShared_6087_ == 0)
{
v___x_6089_ = v___x_6086_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6084_);
v___x_6089_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
return v___x_6089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed(lean_object* v_stx_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_, lean_object* v_a_6126_, lean_object* v_a_6127_, lean_object* v_a_6128_){
_start:
{
lean_object* v_res_6129_; 
v_res_6129_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases(v_stx_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_, v_a_6124_, v_a_6125_, v_a_6126_, v_a_6127_);
lean_dec(v_a_6127_);
lean_dec_ref(v_a_6126_);
lean_dec(v_a_6125_);
lean_dec_ref(v_a_6124_);
lean_dec(v_a_6123_);
lean_dec_ref(v_a_6122_);
lean_dec(v_a_6121_);
lean_dec_ref(v_a_6120_);
return v_res_6129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(size_t v_sz_6130_, size_t v_i_6131_, lean_object* v_bs_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
lean_object* v___x_6142_; 
v___x_6142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___redArg(v_sz_6130_, v_i_6131_, v_bs_6132_, v___y_6137_, v___y_6139_, v___y_6140_);
return v___x_6142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1___boxed(lean_object* v_sz_6143_, lean_object* v_i_6144_, lean_object* v_bs_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
size_t v_sz_boxed_6155_; size_t v_i_boxed_6156_; lean_object* v_res_6157_; 
v_sz_boxed_6155_ = lean_unbox_usize(v_sz_6143_);
lean_dec(v_sz_6143_);
v_i_boxed_6156_ = lean_unbox_usize(v_i_6144_);
lean_dec(v_i_6144_);
v_res_6157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__1(v_sz_boxed_6155_, v_i_boxed_6156_, v_bs_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
lean_dec(v___y_6151_);
lean_dec_ref(v___y_6150_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
return v_res_6157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1(){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6194_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___closed__1));
v___x_6196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___closed__12));
v___x_6197_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___boxed), 10, 0);
v___x_6198_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6194_, v___x_6195_, v___x_6196_, v___x_6197_);
return v___x_6198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1___boxed(lean_object* v_a_6199_){
_start:
{
lean_object* v_res_6200_; 
v_res_6200_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases__1();
return v_res_6200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(lean_object* v___x_6201_, lean_object* v___x_6202_, lean_object* v_a_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v___x_6213_; 
v___x_6213_ = l_Lean_Elab_Tactic_RCases_rcases(v___x_6201_, v___x_6202_, v_a_6203_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
if (lean_obj_tag(v___x_6213_) == 0)
{
lean_object* v_a_6214_; lean_object* v___x_6215_; 
v_a_6214_ = lean_ctor_get(v___x_6213_, 0);
lean_inc(v_a_6214_);
lean_dec_ref_known(v___x_6213_, 1);
v___x_6215_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6214_, v___y_6205_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
return v___x_6215_;
}
else
{
lean_object* v_a_6216_; lean_object* v___x_6218_; uint8_t v_isShared_6219_; uint8_t v_isSharedCheck_6223_; 
v_a_6216_ = lean_ctor_get(v___x_6213_, 0);
v_isSharedCheck_6223_ = !lean_is_exclusive(v___x_6213_);
if (v_isSharedCheck_6223_ == 0)
{
v___x_6218_ = v___x_6213_;
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
else
{
lean_inc(v_a_6216_);
lean_dec(v___x_6213_);
v___x_6218_ = lean_box(0);
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
v_resetjp_6217_:
{
lean_object* v___x_6221_; 
if (v_isShared_6219_ == 0)
{
v___x_6221_ = v___x_6218_;
goto v_reusejp_6220_;
}
else
{
lean_object* v_reuseFailAlloc_6222_; 
v_reuseFailAlloc_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6222_, 0, v_a_6216_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed(lean_object* v___x_6224_, lean_object* v___x_6225_, lean_object* v_a_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
lean_object* v_res_6236_; 
v_res_6236_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0(v___x_6224_, v___x_6225_, v_a_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
return v_res_6236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(lean_object* v___y_6237_, lean_object* v_val_6238_, lean_object* v_a_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_){
_start:
{
lean_object* v___x_6249_; 
v___x_6249_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_obtainNone(v___y_6237_, v_val_6238_, v_a_6239_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
if (lean_obj_tag(v___x_6249_) == 0)
{
lean_object* v_a_6250_; lean_object* v___x_6251_; 
v_a_6250_ = lean_ctor_get(v___x_6249_, 0);
lean_inc(v_a_6250_);
lean_dec_ref_known(v___x_6249_, 1);
v___x_6251_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6250_, v___y_6241_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
return v___x_6251_;
}
else
{
lean_object* v_a_6252_; lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6259_; 
v_a_6252_ = lean_ctor_get(v___x_6249_, 0);
v_isSharedCheck_6259_ = !lean_is_exclusive(v___x_6249_);
if (v_isSharedCheck_6259_ == 0)
{
v___x_6254_ = v___x_6249_;
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
else
{
lean_inc(v_a_6252_);
lean_dec(v___x_6249_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6259_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
lean_object* v___x_6257_; 
if (v_isShared_6255_ == 0)
{
v___x_6257_ = v___x_6254_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_a_6252_);
v___x_6257_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
return v___x_6257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed(lean_object* v___y_6260_, lean_object* v_val_6261_, lean_object* v_a_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_){
_start:
{
lean_object* v_res_6272_; 
v_res_6272_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1(v___y_6260_, v_val_6261_, v_a_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
return v_res_6272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(lean_object* v_msg_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_){
_start:
{
lean_object* v_ref_6279_; lean_object* v___x_6280_; lean_object* v_a_6281_; lean_object* v___x_6283_; uint8_t v_isShared_6284_; uint8_t v_isSharedCheck_6289_; 
v_ref_6279_ = lean_ctor_get(v___y_6276_, 5);
v___x_6280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_processConstructors_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_msg_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
v_a_6281_ = lean_ctor_get(v___x_6280_, 0);
v_isSharedCheck_6289_ = !lean_is_exclusive(v___x_6280_);
if (v_isSharedCheck_6289_ == 0)
{
v___x_6283_ = v___x_6280_;
v_isShared_6284_ = v_isSharedCheck_6289_;
goto v_resetjp_6282_;
}
else
{
lean_inc(v_a_6281_);
lean_dec(v___x_6280_);
v___x_6283_ = lean_box(0);
v_isShared_6284_ = v_isSharedCheck_6289_;
goto v_resetjp_6282_;
}
v_resetjp_6282_:
{
lean_object* v___x_6285_; lean_object* v___x_6287_; 
lean_inc(v_ref_6279_);
v___x_6285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6285_, 0, v_ref_6279_);
lean_ctor_set(v___x_6285_, 1, v_a_6281_);
if (v_isShared_6284_ == 0)
{
lean_ctor_set_tag(v___x_6283_, 1);
lean_ctor_set(v___x_6283_, 0, v___x_6285_);
v___x_6287_ = v___x_6283_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v___x_6285_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg___boxed(lean_object* v_msg_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
lean_dec(v___y_6292_);
lean_dec_ref(v___y_6291_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(size_t v_sz_6297_, size_t v_i_6298_, lean_object* v_bs_6299_){
_start:
{
uint8_t v___x_6300_; 
v___x_6300_ = lean_usize_dec_lt(v_i_6298_, v_sz_6297_);
if (v___x_6300_ == 0)
{
return v_bs_6299_;
}
else
{
lean_object* v_v_6301_; lean_object* v___x_6302_; lean_object* v_bs_x27_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; size_t v___x_6306_; size_t v___x_6307_; lean_object* v___x_6308_; 
v_v_6301_ = lean_array_uget(v_bs_6299_, v_i_6298_);
v___x_6302_ = lean_unsigned_to_nat(0u);
v_bs_x27_6303_ = lean_array_uset(v_bs_6299_, v_i_6298_, v___x_6302_);
v___x_6304_ = lean_box(0);
v___x_6305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6305_, 0, v___x_6304_);
lean_ctor_set(v___x_6305_, 1, v_v_6301_);
v___x_6306_ = ((size_t)1ULL);
v___x_6307_ = lean_usize_add(v_i_6298_, v___x_6306_);
v___x_6308_ = lean_array_uset(v_bs_x27_6303_, v_i_6298_, v___x_6305_);
v_i_6298_ = v___x_6307_;
v_bs_6299_ = v___x_6308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0___boxed(lean_object* v_sz_6310_, lean_object* v_i_6311_, lean_object* v_bs_6312_){
_start:
{
size_t v_sz_boxed_6313_; size_t v_i_boxed_6314_; lean_object* v_res_6315_; 
v_sz_boxed_6313_ = lean_unbox_usize(v_sz_6310_);
lean_dec(v_sz_6310_);
v_i_boxed_6314_ = lean_unbox_usize(v_i_6311_);
lean_dec(v_i_6311_);
v_res_6315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_boxed_6313_, v_i_boxed_6314_, v_bs_6312_);
return v_res_6315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5(void){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__4));
v___x_6327_ = l_Lean_stringToMessageData(v___x_6326_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(lean_object* v_stx_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_, lean_object* v_a_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_){
_start:
{
lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v___x_6361_; uint8_t v___x_6362_; 
v___x_6361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
lean_inc(v_stx_6328_);
v___x_6362_ = l_Lean_Syntax_isOfKind(v_stx_6328_, v___x_6361_);
if (v___x_6362_ == 0)
{
lean_object* v___x_6363_; 
lean_dec(v_stx_6328_);
v___x_6363_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6363_;
}
else
{
lean_object* v___x_6364_; lean_object* v_tk_6365_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; lean_object* v___y_6376_; lean_object* v___y_6377_; lean_object* v___y_6396_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___y_6401_; lean_object* v___y_6402_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v___y_6405_; lean_object* v_a_6406_; lean_object* v___y_6420_; lean_object* v___y_6421_; lean_object* v_val_x3f_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v___y_6427_; lean_object* v___y_6428_; lean_object* v___y_6429_; lean_object* v___y_6430_; lean_object* v___x_6450_; lean_object* v___y_6452_; lean_object* v___y_6453_; lean_object* v_ty_x3f_6454_; lean_object* v___y_6455_; lean_object* v___y_6456_; lean_object* v___y_6457_; lean_object* v___y_6458_; lean_object* v___y_6459_; lean_object* v___y_6460_; lean_object* v___y_6461_; lean_object* v___y_6462_; lean_object* v_pat_x3f_6473_; lean_object* v___y_6474_; lean_object* v___y_6475_; lean_object* v___y_6476_; lean_object* v___y_6477_; lean_object* v___y_6478_; lean_object* v___y_6479_; lean_object* v___y_6480_; lean_object* v___y_6481_; lean_object* v___x_6490_; uint8_t v___x_6491_; 
v___x_6364_ = lean_unsigned_to_nat(0u);
v_tk_6365_ = l_Lean_Syntax_getArg(v_stx_6328_, v___x_6364_);
v___x_6450_ = lean_unsigned_to_nat(1u);
v___x_6490_ = l_Lean_Syntax_getArg(v_stx_6328_, v___x_6450_);
v___x_6491_ = l_Lean_Syntax_isNone(v___x_6490_);
if (v___x_6491_ == 0)
{
uint8_t v___x_6492_; 
lean_inc(v___x_6490_);
v___x_6492_ = l_Lean_Syntax_matchesNull(v___x_6490_, v___x_6450_);
if (v___x_6492_ == 0)
{
lean_object* v___x_6493_; 
lean_dec(v___x_6490_);
lean_dec(v_tk_6365_);
lean_dec(v_stx_6328_);
v___x_6493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6493_;
}
else
{
lean_object* v_pat_x3f_6494_; 
v_pat_x3f_6494_ = l_Lean_Syntax_getArg(v___x_6490_, v___x_6364_);
lean_dec(v___x_6490_);
if (v___x_6491_ == 0)
{
lean_object* v___x_6497_; uint8_t v___x_6498_; 
v___x_6497_ = ((lean_object*)(l_Lean_Elab_Tactic_RCases_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___closed__1));
lean_inc(v_pat_x3f_6494_);
v___x_6498_ = l_Lean_Syntax_isOfKind(v_pat_x3f_6494_, v___x_6497_);
if (v___x_6498_ == 0)
{
lean_object* v___x_6499_; 
lean_dec(v_pat_x3f_6494_);
lean_dec(v_tk_6365_);
lean_dec(v_stx_6328_);
v___x_6499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6499_;
}
else
{
goto v___jp_6495_;
}
}
else
{
goto v___jp_6495_;
}
v___jp_6495_:
{
lean_object* v___x_6496_; 
v___x_6496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6496_, 0, v_pat_x3f_6494_);
v_pat_x3f_6473_ = v___x_6496_;
v___y_6474_ = v_a_6329_;
v___y_6475_ = v_a_6330_;
v___y_6476_ = v_a_6331_;
v___y_6477_ = v_a_6332_;
v___y_6478_ = v_a_6333_;
v___y_6479_ = v_a_6334_;
v___y_6480_ = v_a_6335_;
v___y_6481_ = v_a_6336_;
goto v___jp_6472_;
}
}
}
else
{
lean_object* v___x_6500_; 
lean_dec(v___x_6490_);
v___x_6500_ = lean_box(0);
v_pat_x3f_6473_ = v___x_6500_;
v___y_6474_ = v_a_6329_;
v___y_6475_ = v_a_6330_;
v___y_6476_ = v_a_6331_;
v___y_6477_ = v_a_6332_;
v___y_6478_ = v_a_6333_;
v___y_6479_ = v_a_6334_;
v___y_6480_ = v_a_6335_;
v___y_6481_ = v_a_6336_;
goto v___jp_6472_;
}
v___jp_6366_:
{
lean_object* v___x_6378_; 
v___x_6378_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6370_, v___y_6368_, v___y_6367_, v___y_6369_, v___y_6372_);
if (lean_obj_tag(v___x_6378_) == 0)
{
lean_object* v_a_6379_; lean_object* v___x_6380_; size_t v_sz_6381_; lean_object* v___x_6382_; size_t v___x_6383_; lean_object* v___x_6384_; lean_object* v___f_6385_; lean_object* v___x_6386_; 
v_a_6379_ = lean_ctor_get(v___x_6378_, 0);
lean_inc_n(v_a_6379_, 2);
lean_dec_ref_known(v___x_6378_, 1);
v___x_6380_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_6373_);
lean_dec_ref(v___y_6373_);
v_sz_6381_ = lean_array_size(v___x_6380_);
v___x_6382_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_typed_x3f(v_tk_6365_, v___y_6377_, v___y_6376_);
lean_dec(v___y_6376_);
v___x_6383_ = ((size_t)0ULL);
v___x_6384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__0(v_sz_6381_, v___x_6383_, v___x_6380_);
v___f_6385_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6385_, 0, v___x_6384_);
lean_closure_set(v___f_6385_, 1, v___x_6382_);
lean_closure_set(v___f_6385_, 2, v_a_6379_);
v___x_6386_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6379_, v___f_6385_, v___y_6371_, v___y_6370_, v___y_6375_, v___y_6374_, v___y_6368_, v___y_6367_, v___y_6369_, v___y_6372_);
return v___x_6386_;
}
else
{
lean_object* v_a_6387_; lean_object* v___x_6389_; uint8_t v_isShared_6390_; uint8_t v_isSharedCheck_6394_; 
lean_dec_ref(v___y_6377_);
lean_dec(v___y_6376_);
lean_dec_ref(v___y_6373_);
lean_dec(v_tk_6365_);
v_a_6387_ = lean_ctor_get(v___x_6378_, 0);
v_isSharedCheck_6394_ = !lean_is_exclusive(v___x_6378_);
if (v_isSharedCheck_6394_ == 0)
{
v___x_6389_ = v___x_6378_;
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
else
{
lean_inc(v_a_6387_);
lean_dec(v___x_6378_);
v___x_6389_ = lean_box(0);
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
v_resetjp_6388_:
{
lean_object* v___x_6392_; 
if (v_isShared_6390_ == 0)
{
v___x_6392_ = v___x_6389_;
goto v_reusejp_6391_;
}
else
{
lean_object* v_reuseFailAlloc_6393_; 
v_reuseFailAlloc_6393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_a_6387_);
v___x_6392_ = v_reuseFailAlloc_6393_;
goto v_reusejp_6391_;
}
v_reusejp_6391_:
{
return v___x_6392_;
}
}
}
}
v___jp_6395_:
{
if (lean_obj_tag(v___y_6402_) == 1)
{
if (lean_obj_tag(v_a_6406_) == 0)
{
lean_object* v_val_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v_val_6407_ = lean_ctor_get(v___y_6402_, 0);
lean_inc(v_val_6407_);
lean_dec_ref_known(v___y_6402_, 1);
v___x_6408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_instInhabited___closed__1));
lean_inc(v_tk_6365_);
v___x_6409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6409_, 0, v_tk_6365_);
lean_ctor_set(v___x_6409_, 1, v___x_6408_);
v___y_6367_ = v___y_6396_;
v___y_6368_ = v___y_6397_;
v___y_6369_ = v___y_6399_;
v___y_6370_ = v___y_6398_;
v___y_6371_ = v___y_6400_;
v___y_6372_ = v___y_6401_;
v___y_6373_ = v_val_6407_;
v___y_6374_ = v___y_6403_;
v___y_6375_ = v___y_6405_;
v___y_6376_ = v___y_6404_;
v___y_6377_ = v___x_6409_;
goto v___jp_6366_;
}
else
{
lean_object* v_val_6410_; lean_object* v_val_6411_; 
v_val_6410_ = lean_ctor_get(v___y_6402_, 0);
lean_inc(v_val_6410_);
lean_dec_ref_known(v___y_6402_, 1);
v_val_6411_ = lean_ctor_get(v_a_6406_, 0);
lean_inc(v_val_6411_);
lean_dec_ref_known(v_a_6406_, 1);
v___y_6367_ = v___y_6396_;
v___y_6368_ = v___y_6397_;
v___y_6369_ = v___y_6399_;
v___y_6370_ = v___y_6398_;
v___y_6371_ = v___y_6400_;
v___y_6372_ = v___y_6401_;
v___y_6373_ = v_val_6410_;
v___y_6374_ = v___y_6403_;
v___y_6375_ = v___y_6405_;
v___y_6376_ = v___y_6404_;
v___y_6377_ = v_val_6411_;
goto v___jp_6366_;
}
}
else
{
lean_dec(v___y_6402_);
if (lean_obj_tag(v___y_6404_) == 1)
{
if (lean_obj_tag(v_a_6406_) == 0)
{
lean_object* v_val_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; 
v_val_6412_ = lean_ctor_get(v___y_6404_, 0);
lean_inc(v_val_6412_);
lean_dec_ref_known(v___y_6404_, 1);
v___x_6413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__3));
v___x_6414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6414_, 0, v_tk_6365_);
lean_ctor_set(v___x_6414_, 1, v___x_6413_);
v___y_6339_ = v_val_6412_;
v___y_6340_ = v___y_6396_;
v___y_6341_ = v___y_6397_;
v___y_6342_ = v___y_6399_;
v___y_6343_ = v___y_6398_;
v___y_6344_ = v___y_6400_;
v___y_6345_ = v___y_6401_;
v___y_6346_ = v___y_6403_;
v___y_6347_ = v___y_6405_;
v___y_6348_ = v___x_6414_;
goto v___jp_6338_;
}
else
{
lean_object* v_val_6415_; lean_object* v_val_6416_; 
lean_dec(v_tk_6365_);
v_val_6415_ = lean_ctor_get(v___y_6404_, 0);
lean_inc(v_val_6415_);
lean_dec_ref_known(v___y_6404_, 1);
v_val_6416_ = lean_ctor_get(v_a_6406_, 0);
lean_inc(v_val_6416_);
lean_dec_ref_known(v_a_6406_, 1);
v___y_6339_ = v_val_6415_;
v___y_6340_ = v___y_6396_;
v___y_6341_ = v___y_6397_;
v___y_6342_ = v___y_6399_;
v___y_6343_ = v___y_6398_;
v___y_6344_ = v___y_6400_;
v___y_6345_ = v___y_6401_;
v___y_6346_ = v___y_6403_;
v___y_6347_ = v___y_6405_;
v___y_6348_ = v_val_6416_;
goto v___jp_6338_;
}
}
else
{
lean_object* v___x_6417_; lean_object* v___x_6418_; 
lean_dec(v_a_6406_);
lean_dec(v___y_6404_);
lean_dec(v_tk_6365_);
v___x_6417_ = lean_obj_once(&l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5, &l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5_once, _init_l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__5);
v___x_6418_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v___x_6417_, v___y_6397_, v___y_6396_, v___y_6399_, v___y_6401_);
return v___x_6418_;
}
}
}
v___jp_6419_:
{
if (lean_obj_tag(v___y_6420_) == 0)
{
lean_object* v___x_6431_; 
v___x_6431_ = lean_box(0);
v___y_6396_ = v___y_6428_;
v___y_6397_ = v___y_6427_;
v___y_6398_ = v___y_6424_;
v___y_6399_ = v___y_6429_;
v___y_6400_ = v___y_6423_;
v___y_6401_ = v___y_6430_;
v___y_6402_ = v_val_x3f_6422_;
v___y_6403_ = v___y_6426_;
v___y_6404_ = v___y_6421_;
v___y_6405_ = v___y_6425_;
v_a_6406_ = v___x_6431_;
goto v___jp_6395_;
}
else
{
lean_object* v_val_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6449_; 
v_val_6432_ = lean_ctor_get(v___y_6420_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v___y_6420_);
if (v_isSharedCheck_6449_ == 0)
{
v___x_6434_ = v___y_6420_;
v_isShared_6435_ = v_isSharedCheck_6449_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_val_6432_);
lean_dec(v___y_6420_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6449_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___x_6436_; 
v___x_6436_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_RCasesPatt_parse(v_val_6432_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
if (lean_obj_tag(v___x_6436_) == 0)
{
lean_object* v_a_6437_; lean_object* v___x_6439_; 
v_a_6437_ = lean_ctor_get(v___x_6436_, 0);
lean_inc(v_a_6437_);
lean_dec_ref_known(v___x_6436_, 1);
if (v_isShared_6435_ == 0)
{
lean_ctor_set(v___x_6434_, 0, v_a_6437_);
v___x_6439_ = v___x_6434_;
goto v_reusejp_6438_;
}
else
{
lean_object* v_reuseFailAlloc_6440_; 
v_reuseFailAlloc_6440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_a_6437_);
v___x_6439_ = v_reuseFailAlloc_6440_;
goto v_reusejp_6438_;
}
v_reusejp_6438_:
{
v___y_6396_ = v___y_6428_;
v___y_6397_ = v___y_6427_;
v___y_6398_ = v___y_6424_;
v___y_6399_ = v___y_6429_;
v___y_6400_ = v___y_6423_;
v___y_6401_ = v___y_6430_;
v___y_6402_ = v_val_x3f_6422_;
v___y_6403_ = v___y_6426_;
v___y_6404_ = v___y_6421_;
v___y_6405_ = v___y_6425_;
v_a_6406_ = v___x_6439_;
goto v___jp_6395_;
}
}
else
{
lean_object* v_a_6441_; lean_object* v___x_6443_; uint8_t v_isShared_6444_; uint8_t v_isSharedCheck_6448_; 
lean_del_object(v___x_6434_);
lean_dec(v_val_x3f_6422_);
lean_dec(v___y_6421_);
lean_dec(v_tk_6365_);
v_a_6441_ = lean_ctor_get(v___x_6436_, 0);
v_isSharedCheck_6448_ = !lean_is_exclusive(v___x_6436_);
if (v_isSharedCheck_6448_ == 0)
{
v___x_6443_ = v___x_6436_;
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
else
{
lean_inc(v_a_6441_);
lean_dec(v___x_6436_);
v___x_6443_ = lean_box(0);
v_isShared_6444_ = v_isSharedCheck_6448_;
goto v_resetjp_6442_;
}
v_resetjp_6442_:
{
lean_object* v___x_6446_; 
if (v_isShared_6444_ == 0)
{
v___x_6446_ = v___x_6443_;
goto v_reusejp_6445_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6441_);
v___x_6446_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6445_;
}
v_reusejp_6445_:
{
return v___x_6446_;
}
}
}
}
}
}
v___jp_6451_:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; uint8_t v___x_6465_; 
v___x_6463_ = lean_unsigned_to_nat(3u);
v___x_6464_ = l_Lean_Syntax_getArg(v_stx_6328_, v___x_6463_);
lean_dec(v_stx_6328_);
v___x_6465_ = l_Lean_Syntax_isNone(v___x_6464_);
if (v___x_6465_ == 0)
{
uint8_t v___x_6466_; 
lean_inc(v___x_6464_);
v___x_6466_ = l_Lean_Syntax_matchesNull(v___x_6464_, v___y_6453_);
if (v___x_6466_ == 0)
{
lean_object* v___x_6467_; 
lean_dec(v___x_6464_);
lean_dec(v_ty_x3f_6454_);
lean_dec(v___y_6452_);
lean_dec(v_tk_6365_);
v___x_6467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6467_;
}
else
{
lean_object* v___x_6468_; lean_object* v_val_x3f_6469_; lean_object* v___x_6470_; 
v___x_6468_ = l_Lean_Syntax_getArg(v___x_6464_, v___x_6450_);
lean_dec(v___x_6464_);
v_val_x3f_6469_ = l_Lean_Syntax_getArgs(v___x_6468_);
lean_dec(v___x_6468_);
v___x_6470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6470_, 0, v_val_x3f_6469_);
v___y_6420_ = v___y_6452_;
v___y_6421_ = v_ty_x3f_6454_;
v_val_x3f_6422_ = v___x_6470_;
v___y_6423_ = v___y_6455_;
v___y_6424_ = v___y_6456_;
v___y_6425_ = v___y_6457_;
v___y_6426_ = v___y_6458_;
v___y_6427_ = v___y_6459_;
v___y_6428_ = v___y_6460_;
v___y_6429_ = v___y_6461_;
v___y_6430_ = v___y_6462_;
goto v___jp_6419_;
}
}
else
{
lean_object* v___x_6471_; 
lean_dec(v___x_6464_);
v___x_6471_ = lean_box(0);
v___y_6420_ = v___y_6452_;
v___y_6421_ = v_ty_x3f_6454_;
v_val_x3f_6422_ = v___x_6471_;
v___y_6423_ = v___y_6455_;
v___y_6424_ = v___y_6456_;
v___y_6425_ = v___y_6457_;
v___y_6426_ = v___y_6458_;
v___y_6427_ = v___y_6459_;
v___y_6428_ = v___y_6460_;
v___y_6429_ = v___y_6461_;
v___y_6430_ = v___y_6462_;
goto v___jp_6419_;
}
}
v___jp_6472_:
{
lean_object* v___x_6482_; lean_object* v___x_6483_; uint8_t v___x_6484_; 
v___x_6482_ = lean_unsigned_to_nat(2u);
v___x_6483_ = l_Lean_Syntax_getArg(v_stx_6328_, v___x_6482_);
v___x_6484_ = l_Lean_Syntax_isNone(v___x_6483_);
if (v___x_6484_ == 0)
{
uint8_t v___x_6485_; 
lean_inc(v___x_6483_);
v___x_6485_ = l_Lean_Syntax_matchesNull(v___x_6483_, v___x_6482_);
if (v___x_6485_ == 0)
{
lean_object* v___x_6486_; 
lean_dec(v___x_6483_);
lean_dec(v_pat_x3f_6473_);
lean_dec(v_tk_6365_);
lean_dec(v_stx_6328_);
v___x_6486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6486_;
}
else
{
lean_object* v_ty_x3f_6487_; lean_object* v___x_6488_; 
v_ty_x3f_6487_ = l_Lean_Syntax_getArg(v___x_6483_, v___x_6450_);
lean_dec(v___x_6483_);
v___x_6488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6488_, 0, v_ty_x3f_6487_);
v___y_6452_ = v_pat_x3f_6473_;
v___y_6453_ = v___x_6482_;
v_ty_x3f_6454_ = v___x_6488_;
v___y_6455_ = v___y_6474_;
v___y_6456_ = v___y_6475_;
v___y_6457_ = v___y_6476_;
v___y_6458_ = v___y_6477_;
v___y_6459_ = v___y_6478_;
v___y_6460_ = v___y_6479_;
v___y_6461_ = v___y_6480_;
v___y_6462_ = v___y_6481_;
goto v___jp_6451_;
}
}
else
{
lean_object* v___x_6489_; 
lean_dec(v___x_6483_);
v___x_6489_ = lean_box(0);
v___y_6452_ = v_pat_x3f_6473_;
v___y_6453_ = v___x_6482_;
v_ty_x3f_6454_ = v___x_6489_;
v___y_6455_ = v___y_6474_;
v___y_6456_ = v___y_6475_;
v___y_6457_ = v___y_6476_;
v___y_6458_ = v___y_6477_;
v___y_6459_ = v___y_6478_;
v___y_6460_ = v___y_6479_;
v___y_6461_ = v___y_6480_;
v___y_6462_ = v___y_6481_;
goto v___jp_6451_;
}
}
}
v___jp_6338_:
{
lean_object* v___x_6349_; 
v___x_6349_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6343_, v___y_6341_, v___y_6340_, v___y_6342_, v___y_6345_);
if (lean_obj_tag(v___x_6349_) == 0)
{
lean_object* v_a_6350_; lean_object* v___f_6351_; lean_object* v___x_6352_; 
v_a_6350_ = lean_ctor_get(v___x_6349_, 0);
lean_inc_n(v_a_6350_, 2);
lean_dec_ref_known(v___x_6349_, 1);
v___f_6351_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6351_, 0, v___y_6348_);
lean_closure_set(v___f_6351_, 1, v___y_6339_);
lean_closure_set(v___f_6351_, 2, v_a_6350_);
v___x_6352_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6350_, v___f_6351_, v___y_6344_, v___y_6343_, v___y_6347_, v___y_6346_, v___y_6341_, v___y_6340_, v___y_6342_, v___y_6345_);
return v___x_6352_;
}
else
{
lean_object* v_a_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6360_; 
lean_dec_ref(v___y_6348_);
lean_dec(v___y_6339_);
v_a_6353_ = lean_ctor_get(v___x_6349_, 0);
v_isSharedCheck_6360_ = !lean_is_exclusive(v___x_6349_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6355_ = v___x_6349_;
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_a_6353_);
lean_dec(v___x_6349_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
lean_object* v___x_6358_; 
if (v_isShared_6356_ == 0)
{
v___x_6358_ = v___x_6355_;
goto v_reusejp_6357_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_a_6353_);
v___x_6358_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6357_;
}
v_reusejp_6357_:
{
return v___x_6358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed(lean_object* v_stx_6501_, lean_object* v_a_6502_, lean_object* v_a_6503_, lean_object* v_a_6504_, lean_object* v_a_6505_, lean_object* v_a_6506_, lean_object* v_a_6507_, lean_object* v_a_6508_, lean_object* v_a_6509_, lean_object* v_a_6510_){
_start:
{
lean_object* v_res_6511_; 
v_res_6511_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain(v_stx_6501_, v_a_6502_, v_a_6503_, v_a_6504_, v_a_6505_, v_a_6506_, v_a_6507_, v_a_6508_, v_a_6509_);
lean_dec(v_a_6509_);
lean_dec_ref(v_a_6508_);
lean_dec(v_a_6507_);
lean_dec_ref(v_a_6506_);
lean_dec(v_a_6505_);
lean_dec_ref(v_a_6504_);
lean_dec(v_a_6503_);
lean_dec_ref(v_a_6502_);
return v_res_6511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(lean_object* v_00_u03b1_6512_, lean_object* v_msg_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_){
_start:
{
lean_object* v___x_6523_; 
v___x_6523_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___redArg(v_msg_6513_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_);
return v___x_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1___boxed(lean_object* v_00_u03b1_6524_, lean_object* v_msg_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_){
_start:
{
lean_object* v_res_6535_; 
v_res_6535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain_spec__1(v_00_u03b1_6524_, v_msg_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_, v___y_6531_, v___y_6532_, v___y_6533_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6532_);
lean_dec(v___y_6531_);
lean_dec_ref(v___y_6530_);
lean_dec(v___y_6529_);
lean_dec_ref(v___y_6528_);
lean_dec(v___y_6527_);
lean_dec_ref(v___y_6526_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1(){
_start:
{
lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; 
v___x_6541_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___closed__1));
v___x_6543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___closed__1));
v___x_6544_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___boxed), 10, 0);
v___x_6545_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6541_, v___x_6542_, v___x_6543_, v___x_6544_);
return v___x_6545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1___boxed(lean_object* v_a_6546_){
_start:
{
lean_object* v_res_6547_; 
v_res_6547_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalObtain__1();
return v_res_6547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(lean_object* v_pats_6548_, lean_object* v_ty_x3f_6549_, lean_object* v_a_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v___x_6560_; 
v___x_6560_ = l_Lean_Elab_Tactic_RCases_rintro(v_pats_6548_, v_ty_x3f_6549_, v_a_6550_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6560_) == 0)
{
lean_object* v_a_6561_; lean_object* v___x_6562_; 
v_a_6561_ = lean_ctor_get(v___x_6560_, 0);
lean_inc(v_a_6561_);
lean_dec_ref_known(v___x_6560_, 1);
v___x_6562_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_6561_, v___y_6552_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
return v___x_6562_;
}
else
{
lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6570_; 
v_a_6563_ = lean_ctor_get(v___x_6560_, 0);
v_isSharedCheck_6570_ = !lean_is_exclusive(v___x_6560_);
if (v_isSharedCheck_6570_ == 0)
{
v___x_6565_ = v___x_6560_;
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_dec(v___x_6560_);
v___x_6565_ = lean_box(0);
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
v_resetjp_6564_:
{
lean_object* v___x_6568_; 
if (v_isShared_6566_ == 0)
{
v___x_6568_ = v___x_6565_;
goto v_reusejp_6567_;
}
else
{
lean_object* v_reuseFailAlloc_6569_; 
v_reuseFailAlloc_6569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_a_6563_);
v___x_6568_ = v_reuseFailAlloc_6569_;
goto v_reusejp_6567_;
}
v_reusejp_6567_:
{
return v___x_6568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed(lean_object* v_pats_6571_, lean_object* v_ty_x3f_6572_, lean_object* v_a_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_){
_start:
{
lean_object* v_res_6583_; 
v_res_6583_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0(v_pats_6571_, v_ty_x3f_6572_, v_a_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
lean_dec(v___y_6581_);
lean_dec_ref(v___y_6580_);
lean_dec(v___y_6579_);
lean_dec_ref(v___y_6578_);
lean_dec(v___y_6577_);
lean_dec_ref(v___y_6576_);
lean_dec(v___y_6575_);
lean_dec_ref(v___y_6574_);
return v_res_6583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(lean_object* v_stx_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_){
_start:
{
lean_object* v___x_6600_; uint8_t v___x_6601_; 
v___x_6600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
lean_inc(v_stx_6590_);
v___x_6601_ = l_Lean_Syntax_isOfKind(v_stx_6590_, v___x_6600_);
if (v___x_6601_ == 0)
{
lean_object* v___x_6602_; 
lean_dec(v_stx_6590_);
v___x_6602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6602_;
}
else
{
lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v_ty_x3f_6606_; lean_object* v___y_6607_; lean_object* v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; lean_object* v___y_6612_; lean_object* v___y_6613_; lean_object* v___y_6614_; lean_object* v___x_6628_; lean_object* v___x_6629_; uint8_t v___x_6630_; 
v___x_6603_ = lean_unsigned_to_nat(1u);
v___x_6604_ = l_Lean_Syntax_getArg(v_stx_6590_, v___x_6603_);
v___x_6628_ = lean_unsigned_to_nat(2u);
v___x_6629_ = l_Lean_Syntax_getArg(v_stx_6590_, v___x_6628_);
lean_dec(v_stx_6590_);
v___x_6630_ = l_Lean_Syntax_isNone(v___x_6629_);
if (v___x_6630_ == 0)
{
uint8_t v___x_6631_; 
lean_inc(v___x_6629_);
v___x_6631_ = l_Lean_Syntax_matchesNull(v___x_6629_, v___x_6628_);
if (v___x_6631_ == 0)
{
lean_object* v___x_6632_; 
lean_dec(v___x_6629_);
lean_dec(v___x_6604_);
v___x_6632_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__0___redArg();
return v___x_6632_;
}
else
{
lean_object* v_ty_x3f_6633_; lean_object* v___x_6634_; 
v_ty_x3f_6633_ = l_Lean_Syntax_getArg(v___x_6629_, v___x_6603_);
lean_dec(v___x_6629_);
v___x_6634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6634_, 0, v_ty_x3f_6633_);
v_ty_x3f_6606_ = v___x_6634_;
v___y_6607_ = v_a_6591_;
v___y_6608_ = v_a_6592_;
v___y_6609_ = v_a_6593_;
v___y_6610_ = v_a_6594_;
v___y_6611_ = v_a_6595_;
v___y_6612_ = v_a_6596_;
v___y_6613_ = v_a_6597_;
v___y_6614_ = v_a_6598_;
goto v___jp_6605_;
}
}
else
{
lean_object* v___x_6635_; 
lean_dec(v___x_6629_);
v___x_6635_ = lean_box(0);
v_ty_x3f_6606_ = v___x_6635_;
v___y_6607_ = v_a_6591_;
v___y_6608_ = v_a_6592_;
v___y_6609_ = v_a_6593_;
v___y_6610_ = v_a_6594_;
v___y_6611_ = v_a_6595_;
v___y_6612_ = v_a_6596_;
v___y_6613_ = v_a_6597_;
v___y_6614_ = v_a_6598_;
goto v___jp_6605_;
}
v___jp_6605_:
{
lean_object* v___x_6615_; 
v___x_6615_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6608_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_);
if (lean_obj_tag(v___x_6615_) == 0)
{
lean_object* v_a_6616_; lean_object* v_pats_6617_; lean_object* v___f_6618_; lean_object* v___x_6619_; 
v_a_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc_n(v_a_6616_, 2);
lean_dec_ref_known(v___x_6615_, 1);
v_pats_6617_ = l_Lean_Syntax_getArgs(v___x_6604_);
lean_dec(v___x_6604_);
v___f_6618_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6618_, 0, v_pats_6617_);
lean_closure_set(v___f_6618_, 1, v_ty_x3f_6606_);
lean_closure_set(v___f_6618_, 2, v_a_6616_);
v___x_6619_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRCases_spec__2___redArg(v_a_6616_, v___f_6618_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_);
return v___x_6619_;
}
else
{
lean_object* v_a_6620_; lean_object* v___x_6622_; uint8_t v_isShared_6623_; uint8_t v_isSharedCheck_6627_; 
lean_dec(v_ty_x3f_6606_);
lean_dec(v___x_6604_);
v_a_6620_ = lean_ctor_get(v___x_6615_, 0);
v_isSharedCheck_6627_ = !lean_is_exclusive(v___x_6615_);
if (v_isSharedCheck_6627_ == 0)
{
v___x_6622_ = v___x_6615_;
v_isShared_6623_ = v_isSharedCheck_6627_;
goto v_resetjp_6621_;
}
else
{
lean_inc(v_a_6620_);
lean_dec(v___x_6615_);
v___x_6622_ = lean_box(0);
v_isShared_6623_ = v_isSharedCheck_6627_;
goto v_resetjp_6621_;
}
v_resetjp_6621_:
{
lean_object* v___x_6625_; 
if (v_isShared_6623_ == 0)
{
v___x_6625_ = v___x_6622_;
goto v_reusejp_6624_;
}
else
{
lean_object* v_reuseFailAlloc_6626_; 
v_reuseFailAlloc_6626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_a_6620_);
v___x_6625_ = v_reuseFailAlloc_6626_;
goto v_reusejp_6624_;
}
v_reusejp_6624_:
{
return v___x_6625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed(lean_object* v_stx_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro(v_stx_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_, v_a_6643_, v_a_6644_);
lean_dec(v_a_6644_);
lean_dec_ref(v_a_6643_);
lean_dec(v_a_6642_);
lean_dec_ref(v_a_6641_);
lean_dec(v_a_6640_);
lean_dec_ref(v_a_6639_);
lean_dec(v_a_6638_);
lean_dec_ref(v_a_6637_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1(){
_start:
{
lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; 
v___x_6652_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___closed__1));
v___x_6654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___closed__1));
v___x_6655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___boxed), 10, 0);
v___x_6656_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6652_, v___x_6653_, v___x_6654_, v___x_6655_);
return v___x_6656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1___boxed(lean_object* v_a_6657_){
_start:
{
lean_object* v_res_6658_; 
v_res_6658_ = l___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro___regBuiltin___private_Lean_Elab_Tactic_RCases_0__Lean_Elab_Tactic_RCases_evalRIntro__1();
return v_res_6658_;
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
