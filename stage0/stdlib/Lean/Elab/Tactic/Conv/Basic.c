// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Basic
// Imports: public import Lean.Meta.Tactic.Replace public import Lean.Elab.Tactic.BuiltinTactic
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_convert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Tactic `conv` failed: There are unsolved goals\n"};
static const lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_convert___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_convert___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "Internal error: Conversion-mode tactic found an invalid `conv` goal"};
static const lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "whnf"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 111, 86, 148, 119, 255, 116, 73)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalWhnf"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(6, 30, 125, 115, 1, 6, 125, 181)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(91) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 127, 28, 249, 1, 118, 43, 106)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalReduce"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 147, 193, 102, 100, 242, 130, 81)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 143, 59, 185, 170, 152, 3, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalZeta"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 15, 219, 249, 19, 201, 139, 5)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 78, 175, 7, 2, 107, 214, 173)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalClear"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 199, 47, 127, 237, 69, 197, 255)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 35, 202, 76, 198, 168, 114, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 70, 8, 168, 147, 123, 69)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(110) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeqBracketed"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 46, 60, 206, 104, 220, 125, 67)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeqBracketed"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(96, 134, 88, 86, 62, 164, 138, 44)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nestedConv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 174, 232, 149, 164, 188, 109, 191)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalNestedConv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 69, 109, 55, 136, 241, 183, 112)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 81, 30, 13, 252, 23, 29, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalConvSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 126, 12, 172, 125, 122, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(124) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convConvSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 85, 97, 250, 95, 212, 248, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalConvConvSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 138, 122, 156, 99, 134, 63)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(129) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(4, 172, 52, 155, 88, 222, 189, 57)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalParen"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 44, 38, 199, 32, 20, 2, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(132) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 23, 62, 30, 134, 160, 158, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalNestedTacticCore"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 57, 78, 97, 88, 231, 178, 80)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(149) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNestedTactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 223, 79, 147, 100, 241, 140, 72)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convTactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 239, 251, 250, 179, 30, 250, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalConvTactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 197, 60, 184, 130, 138, 183, 212)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(160) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 39, 103, 162, 58, 5, 181, 114)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 139, 144, 223, 221, 17, 152, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalConv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 46, 136, 31, 44, 193, 131, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(185) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalFirst___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 113, 181, 219, 229, 158, 34, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalFirst"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 17, 248, 44, 249, 130, 220, 46)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(188) << 1) | 1)),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object* v_e_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_10_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1));
v___x_11_ = lean_unsigned_to_nat(3u);
v___x_12_ = l_Lean_Expr_isAppOfArity(v_e_4_, v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
v___x_13_ = lean_whnf(v_e_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = l_Lean_mkLHSGoalRaw(v_a_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_18_);
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
return v___x_13_;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = l_Lean_mkLHSGoalRaw(v_e_4_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object* v_lhs_32_, lean_object* v_tag_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; 
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc_ref(v_lhs_32_);
v___x_39_ = lean_infer_type(v_lhs_32_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v___x_39_);
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_a_40_);
v___x_42_ = 0;
v___x_43_ = lean_box(0);
v___x_44_ = l_Lean_Meta_mkFreshExprMVar(v___x_41_, v___x_42_, v___x_43_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_n(v_a_45_, 2);
lean_dec_ref(v___x_44_);
v___x_46_ = l_Lean_Meta_mkEq(v_lhs_32_, v_a_45_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = l_Lean_mkLHSGoalRaw(v_a_47_);
v___x_49_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_48_, v_tag_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_58_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_58_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v_a_45_);
lean_ctor_set(v___x_54_, 1, v_a_50_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_54_);
v___x_56_ = v___x_52_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
lean_dec(v_a_45_);
v_a_59_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_49_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_49_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_45_);
lean_dec(v_tag_33_);
v_a_67_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_46_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_46_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_tag_33_);
lean_dec_ref(v_lhs_32_);
v_a_75_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_44_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_44_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec(v_tag_33_);
lean_dec_ref(v_lhs_32_);
v_a_83_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_39_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_39_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor___boxed(lean_object* v_lhs_91_, lean_object* v_tag_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_lhs_91_, v_tag_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object* v_mvarId_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
lean_inc(v_mvarId_99_);
v___x_105_ = l_Lean_MVarId_getType(v_mvarId_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_135_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_135_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_isLHSGoal_x3f(v_a_106_);
lean_dec(v_a_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
lean_del_object(v___x_108_);
lean_inc(v_mvarId_99_);
v___x_111_ = l_Lean_MVarId_getType(v_mvarId_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v___x_111_);
v___x_113_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_112_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref(v___x_113_);
v___x_115_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_99_, v_a_114_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_115_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_mvarId_99_);
v_a_116_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_113_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_mvarId_99_);
v_a_124_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_111_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_111_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec_ref(v___x_110_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v_mvarId_99_);
v___x_133_ = v___x_108_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_mvarId_99_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_mvarId_99_);
v_a_136_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_105_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_105_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___boxed(lean_object* v_mvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_mvarId_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(lean_object* v_e_151_, lean_object* v___y_152_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_Expr_hasMVar(v_e_151_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v_e_151_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v_mctx_157_; lean_object* v___x_158_; lean_object* v_fst_159_; lean_object* v_snd_160_; lean_object* v___x_161_; lean_object* v_cache_162_; lean_object* v_zetaDeltaFVarIds_163_; lean_object* v_postponed_164_; lean_object* v_diag_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_174_; 
v___x_156_ = lean_st_ref_get(v___y_152_);
v_mctx_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc_ref(v_mctx_157_);
lean_dec(v___x_156_);
v___x_158_ = l_Lean_instantiateMVarsCore(v_mctx_157_, v_e_151_);
v_fst_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_fst_159_);
v_snd_160_ = lean_ctor_get(v___x_158_, 1);
lean_inc(v_snd_160_);
lean_dec_ref(v___x_158_);
v___x_161_ = lean_st_ref_take(v___y_152_);
v_cache_162_ = lean_ctor_get(v___x_161_, 1);
v_zetaDeltaFVarIds_163_ = lean_ctor_get(v___x_161_, 2);
v_postponed_164_ = lean_ctor_get(v___x_161_, 3);
v_diag_165_ = lean_ctor_get(v___x_161_, 4);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_161_, 0);
lean_dec(v_unused_175_);
v___x_167_ = v___x_161_;
v_isShared_168_ = v_isSharedCheck_174_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_diag_165_);
lean_inc(v_postponed_164_);
lean_inc(v_zetaDeltaFVarIds_163_);
lean_inc(v_cache_162_);
lean_dec(v___x_161_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_174_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v_snd_160_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_snd_160_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_cache_162_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_zetaDeltaFVarIds_163_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_postponed_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_diag_165_);
v___x_170_ = v_reuseFailAlloc_173_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_st_ref_set(v___y_152_, v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_fst_159_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg___boxed(lean_object* v_e_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_e_176_, v___y_177_);
lean_dec(v___y_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(lean_object* v_e_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_e_180_, v___y_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___boxed(lean_object* v_e_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(v_e_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0(lean_object* v_____r_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0___boxed(lean_object* v_____r_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(v_____r_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(lean_object* v_as_x27_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
if (lean_obj_tag(v_as_x27_225_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_b_226_);
return v___x_232_;
}
else
{
lean_object* v_head_233_; lean_object* v_tail_234_; lean_object* v___x_235_; 
v_head_233_ = lean_ctor_get(v_as_x27_225_, 0);
lean_inc(v_head_233_);
v_tail_234_ = lean_ctor_get(v_as_x27_225_, 1);
lean_inc(v_tail_234_);
lean_dec_ref(v_as_x27_225_);
v___x_235_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v___y_239_; lean_object* v___y_242_; lean_object* v___y_243_; uint8_t v___y_244_; uint8_t v___x_247_; lean_object* v___x_248_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = lean_box(0);
v___x_247_ = 1;
lean_inc(v_head_233_);
v___x_248_ = l_Lean_MVarId_refl(v_head_233_, v___x_247_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_dec(v_a_236_);
lean_dec(v_head_233_);
v___y_239_ = v___x_248_;
goto v___jp_238_;
}
else
{
lean_object* v_a_249_; uint8_t v___y_251_; uint8_t v___x_267_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
v___x_267_ = l_Lean_Exception_isInterrupt(v_a_249_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Exception_isRuntime(v_a_249_);
v___y_251_ = v___x_268_;
goto v___jp_250_;
}
else
{
lean_dec(v_a_249_);
v___y_251_ = v___x_267_;
goto v___jp_250_;
}
v___jp_250_:
{
if (v___y_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v___x_248_);
v___x_252_ = l_Lean_Meta_SavedState_restore___redArg(v_a_236_, v___y_228_, v___y_230_);
lean_dec(v_a_236_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v___x_252_);
v___x_253_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref(v___x_253_);
v___x_255_ = l_Lean_MVarId_inferInstance(v_head_233_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_dec(v_a_254_);
v___y_239_ = v___x_255_;
goto v___jp_238_;
}
else
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v___x_257_ = l_Lean_Exception_isInterrupt(v_a_256_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Exception_isRuntime(v_a_256_);
v___y_242_ = v_a_254_;
v___y_243_ = v___x_255_;
v___y_244_ = v___x_258_;
goto v___jp_241_;
}
else
{
lean_dec(v_a_256_);
v___y_242_ = v_a_254_;
v___y_243_ = v___x_255_;
v___y_244_ = v___x_257_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_tail_234_);
lean_dec(v_head_233_);
v_a_259_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_253_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_253_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_dec(v_head_233_);
v___y_239_ = v___x_252_;
goto v___jp_238_;
}
}
else
{
lean_dec(v_a_236_);
lean_dec(v_head_233_);
v___y_239_ = v___x_248_;
goto v___jp_238_;
}
}
}
v___jp_238_:
{
if (lean_obj_tag(v___y_239_) == 0)
{
lean_dec_ref(v___y_239_);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_237_;
goto _start;
}
else
{
lean_dec(v_tail_234_);
return v___y_239_;
}
}
v___jp_241_:
{
if (v___y_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec_ref(v___y_243_);
v___x_245_ = l_Lean_Meta_SavedState_restore___redArg(v___y_242_, v___y_228_, v___y_230_);
lean_dec_ref(v___y_242_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_dec_ref(v___x_245_);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_237_;
goto _start;
}
else
{
v___y_239_ = v___x_245_;
goto v___jp_238_;
}
}
else
{
lean_dec_ref(v___y_242_);
v___y_239_ = v___y_243_;
goto v___jp_238_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_tail_234_);
lean_dec(v_head_233_);
v_a_269_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_235_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_235_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(lean_object* v_as_x27_277_, lean_object* v_b_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_277_, v_b_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(lean_object* v_msgData_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v_env_292_; lean_object* v___x_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_291_ = lean_st_ref_get(v___y_289_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
lean_dec(v___x_291_);
v___x_293_ = lean_st_ref_get(v___y_287_);
v_mctx_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_293_);
v_lctx_295_ = lean_ctor_get(v___y_286_, 2);
v_options_296_ = lean_ctor_get(v___y_288_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_292_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_285_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_ref_313_; lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_ref_313_ = lean_ctor_get(v___y_310_, 5);
v___x_314_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc(v_ref_313_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_ref_313_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 1);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_convert___closed__0));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object* v_lhs_334_, lean_object* v_conv_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_lhs_334_, v___x_345_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_432_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v_fst_348_ = lean_ctor_get(v_a_347_, 0);
v_snd_349_ = lean_ctor_get(v_a_347_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_432_ == 0)
{
v___x_351_ = v_a_347_;
v_isShared_352_ = v_isSharedCheck_432_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_inc(v_fst_348_);
lean_dec(v_a_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_432_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v_a_356_; lean_object* v___y_375_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
v___x_400_ = l_Lean_Expr_mvarId_x21(v_snd_349_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_402_, v_a_337_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
lean_dec_ref(v___x_403_);
lean_inc(v_a_343_);
lean_inc_ref(v_a_342_);
lean_inc(v_a_341_);
lean_inc_ref(v_a_340_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
v___x_404_ = lean_apply_9(v_conv_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, lean_box(0));
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_404_);
v___x_405_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = lean_box(0);
v___x_408_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_a_406_, v___x_407_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_408_);
v___x_409_ = l_Lean_Elab_Tactic_pruneSolvedGoals(v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
lean_dec_ref(v___x_409_);
v___x_410_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v___x_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref(v___x_410_);
v___x_412_ = l_List_isEmpty___redArg(v_a_411_);
lean_dec(v_a_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref(v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_convert___closed__1, &l_Lean_Elab_Tactic_Conv_convert___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_convert___closed__1);
v___x_416_ = l_Lean_Elab_goalsToMessageData(v_a_414_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v___x_417_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
v___y_375_ = v___x_418_;
goto v___jp_374_;
}
else
{
lean_object* v_a_419_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_419_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_413_);
v_a_356_ = v_a_419_;
goto v___jp_355_;
}
}
else
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(v___x_407_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
v___y_375_ = v___x_420_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_421_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_421_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_421_);
lean_dec_ref(v___x_410_);
v_a_356_ = v_a_421_;
goto v___jp_355_;
}
}
else
{
v___y_375_ = v___x_409_;
goto v___jp_374_;
}
}
else
{
v___y_375_ = v___x_408_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_422_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_422_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_405_);
v_a_356_ = v_a_422_;
goto v___jp_355_;
}
}
else
{
lean_object* v_a_423_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_423_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_423_);
lean_dec_ref(v___x_404_);
v_a_356_ = v_a_423_;
goto v___jp_355_;
}
}
else
{
lean_dec_ref(v_conv_335_);
v___y_375_ = v___x_403_;
goto v___jp_374_;
}
v___jp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_354_, v_a_337_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_365_);
v___x_359_ = v___x_357_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_dec(v___x_357_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v_a_356_);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_356_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_a_356_);
v_a_366_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_357_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_357_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
v___jp_374_:
{
if (lean_obj_tag(v___y_375_) == 0)
{
lean_object* v___x_376_; 
lean_dec_ref(v___y_375_);
v___x_376_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_354_, v_a_337_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v___x_376_);
v___x_377_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_fst_348_, v_a_341_);
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v___x_377_);
v___x_379_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_snd_349_, v_a_341_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_390_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_a_380_);
lean_ctor_set(v___x_351_, 0, v_a_378_);
v___x_385_ = v___x_351_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_a_380_);
v___x_385_ = v_reuseFailAlloc_389_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_391_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_376_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_376_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_399_ = lean_ctor_get(v___y_375_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___y_375_);
v_a_356_ = v_a_399_;
goto v___jp_355_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
lean_dec_ref(v_conv_335_);
v_a_424_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_353_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_353_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_dec_ref(v_conv_335_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___boxed(lean_object* v_lhs_433_, lean_object* v_conv_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_Tactic_Conv_convert(v_lhs_433_, v_conv_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(lean_object* v_as_445_, lean_object* v_as_x27_446_, lean_object* v_b_447_, lean_object* v_a_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_446_, v_b_447_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(lean_object* v_as_459_, lean_object* v_as_x27_460_, lean_object* v_b_461_, lean_object* v_a_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(v_as_459_, v_as_x27_460_, v_b_461_, v_a_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v_as_459_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(lean_object* v_00_u03b1_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_474_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(lean_object* v_00_u03b1_485_, lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(v_00_u03b1_485_, v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_504_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_504_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(lean_object* v_mvarId_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_521_, v_x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(lean_object* v_00_u03b1_529_, lean_object* v_mvarId_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(lean_object* v_00_u03b1_538_, lean_object* v_mvarId_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(v_00_u03b1_538_, v_mvarId_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_ref_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_ref_553_ = lean_ctor_get(v___y_550_, 5);
v___x_554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_inc(v_ref_553_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_ref_553_);
lean_ctor_set(v___x_559_, 1, v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 1);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(lean_object* v_mvarId_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_MVarId_getType(v_mvarId_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_Meta_matchEq_x3f(v_a_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_594_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_594_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 1)
{
lean_object* v_val_587_; lean_object* v_snd_588_; lean_object* v___x_590_; 
v_val_587_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_val_587_);
lean_dec_ref(v_a_583_);
v_snd_588_ = lean_ctor_get(v_val_587_, 1);
lean_inc(v_snd_588_);
lean_dec(v_val_587_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_snd_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_snd_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_del_object(v___x_585_);
lean_dec(v_a_583_);
v___x_592_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1);
v___x_593_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v___x_592_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_593_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_582_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_582_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_580_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_580_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(lean_object* v_mvarId_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(v_mvarId_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object* v_mvarId_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___f_624_; lean_object* v___x_625_; 
lean_inc(v_mvarId_618_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_624_, 0, v_mvarId_618_);
v___x_625_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_618_, v___f_624_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(lean_object* v_mvarId_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(lean_object* v_00_u03b1_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(v_00_u03b1_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_656_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_674_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Elab_Tactic_Conv_getLhsRhs(v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v___x_706_; 
v_fst_704_ = lean_ctor_get(v_a_700_, 0);
lean_inc(v_fst_704_);
lean_dec(v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v_fst_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_699_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_699_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_725_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Elab_Tactic_Conv_getLhs(v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_759_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_759_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_snd_755_; lean_object* v___x_757_; 
v_snd_755_ = lean_ctor_get(v_a_751_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_snd_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_snd_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_750_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_776_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Elab_Tactic_Conv_getRhs(v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_ks_799_; lean_object* v_vs_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_824_; 
v_ks_799_ = lean_ctor_get(v_x_795_, 0);
v_vs_800_ = lean_ctor_get(v_x_795_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_824_ == 0)
{
v___x_802_ = v_x_795_;
v_isShared_803_ = v_isSharedCheck_824_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_vs_800_);
lean_inc(v_ks_799_);
lean_dec(v_x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_824_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_array_get_size(v_ks_799_);
v___x_805_ = lean_nat_dec_lt(v_x_796_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v_x_796_);
v___x_806_ = lean_array_push(v_ks_799_, v_x_797_);
v___x_807_ = lean_array_push(v_vs_800_, v_x_798_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_807_);
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_809_ = v___x_802_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v_k_x27_811_; uint8_t v___x_812_; 
v_k_x27_811_ = lean_array_fget_borrowed(v_ks_799_, v_x_796_);
v___x_812_ = l_Lean_instBEqMVarId_beq(v_x_797_, v_k_x27_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_814_; 
if (v_isShared_803_ == 0)
{
v___x_814_ = v___x_802_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_ks_799_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_vs_800_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_x_796_, v___x_815_);
lean_dec(v_x_796_);
v_x_795_ = v___x_814_;
v_x_796_ = v___x_816_;
goto _start;
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = lean_array_fset(v_ks_799_, v_x_796_, v_x_797_);
v___x_820_ = lean_array_fset(v_vs_800_, v_x_796_, v_x_798_);
lean_dec(v_x_796_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_820_);
lean_ctor_set(v___x_802_, 0, v___x_819_);
v___x_822_ = v___x_802_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_825_, lean_object* v_k_826_, lean_object* v_v_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_825_, v___x_828_, v_k_826_, v_v_827_);
return v___x_829_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; 
v___x_830_ = ((size_t)5ULL);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_shift_left(v___x_831_, v___x_830_);
return v___x_832_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; 
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_835_ = lean_usize_sub(v___x_834_, v___x_833_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(lean_object* v_x_837_, size_t v_x_838_, size_t v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
lean_object* v_es_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v_j_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_es_842_ = lean_ctor_get(v_x_837_, 0);
v___x_843_ = ((size_t)5ULL);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_846_ = lean_usize_land(v_x_838_, v___x_845_);
v_j_847_ = lean_usize_to_nat(v___x_846_);
v___x_848_ = lean_array_get_size(v_es_842_);
v___x_849_ = lean_nat_dec_lt(v_j_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec(v_j_847_);
lean_dec(v_x_841_);
lean_dec(v_x_840_);
return v_x_837_;
}
else
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_886_; 
lean_inc_ref(v_es_842_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_x_837_, 0);
lean_dec(v_unused_887_);
v___x_851_ = v_x_837_;
v_isShared_852_ = v_isSharedCheck_886_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_x_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_886_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_v_853_; lean_object* v___x_854_; lean_object* v_xs_x27_855_; lean_object* v___y_857_; 
v_v_853_ = lean_array_fget(v_es_842_, v_j_847_);
v___x_854_ = lean_box(0);
v_xs_x27_855_ = lean_array_fset(v_es_842_, v_j_847_, v___x_854_);
switch(lean_obj_tag(v_v_853_))
{
case 0:
{
lean_object* v_key_862_; lean_object* v_val_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_key_862_ = lean_ctor_get(v_v_853_, 0);
v_val_863_ = lean_ctor_get(v_v_853_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_v_853_);
if (v_isSharedCheck_873_ == 0)
{
v___x_865_ = v_v_853_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_val_863_);
lean_inc(v_key_862_);
lean_dec(v_v_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_instBEqMVarId_beq(v_x_840_, v_key_862_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_del_object(v___x_865_);
v___x_868_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_862_, v_val_863_, v_x_840_, v_x_841_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___y_857_ = v___x_869_;
goto v___jp_856_;
}
else
{
lean_object* v___x_871_; 
lean_dec(v_val_863_);
lean_dec(v_key_862_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v_x_841_);
lean_ctor_set(v___x_865_, 0, v_x_840_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_x_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_x_841_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v___y_857_ = v___x_871_;
goto v___jp_856_;
}
}
}
}
case 1:
{
lean_object* v_node_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_884_; 
v_node_874_ = lean_ctor_get(v_v_853_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_v_853_);
if (v_isSharedCheck_884_ == 0)
{
v___x_876_ = v_v_853_;
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_node_874_);
lean_dec(v_v_853_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_878_ = lean_usize_shift_right(v_x_838_, v___x_843_);
v___x_879_ = lean_usize_add(v_x_839_, v___x_844_);
v___x_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_node_874_, v___x_878_, v___x_879_, v_x_840_, v_x_841_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_880_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v___y_857_ = v___x_882_;
goto v___jp_856_;
}
}
}
default: 
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_x_840_);
lean_ctor_set(v___x_885_, 1, v_x_841_);
v___y_857_ = v___x_885_;
goto v___jp_856_;
}
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_array_fset(v_xs_x27_855_, v_j_847_, v___y_857_);
lean_dec(v_j_847_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_858_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
else
{
lean_object* v_ks_888_; lean_object* v_vs_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_909_; 
v_ks_888_ = lean_ctor_get(v_x_837_, 0);
v_vs_889_ = lean_ctor_get(v_x_837_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_909_ == 0)
{
v___x_891_ = v_x_837_;
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_vs_889_);
lean_inc(v_ks_888_);
lean_dec(v_x_837_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_ks_888_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_vs_889_);
v___x_894_ = v_reuseFailAlloc_908_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v_newNode_895_; uint8_t v___y_897_; size_t v___x_903_; uint8_t v___x_904_; 
v_newNode_895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v___x_894_, v_x_840_, v_x_841_);
v___x_903_ = ((size_t)7ULL);
v___x_904_ = lean_usize_dec_le(v___x_903_, v_x_839_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_895_);
v___x_906_ = lean_unsigned_to_nat(4u);
v___x_907_ = lean_nat_dec_lt(v___x_905_, v___x_906_);
lean_dec(v___x_905_);
v___y_897_ = v___x_907_;
goto v___jp_896_;
}
else
{
v___y_897_ = v___x_904_;
goto v___jp_896_;
}
v___jp_896_:
{
if (v___y_897_ == 0)
{
lean_object* v_ks_898_; lean_object* v_vs_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_ks_898_ = lean_ctor_get(v_newNode_895_, 0);
lean_inc_ref(v_ks_898_);
v_vs_899_ = lean_ctor_get(v_newNode_895_, 1);
lean_inc_ref(v_vs_899_);
lean_dec_ref(v_newNode_895_);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_x_839_, v_ks_898_, v_vs_899_, v___x_900_, v___x_901_);
lean_dec_ref(v_vs_899_);
lean_dec_ref(v_ks_898_);
return v___x_902_;
}
else
{
return v_newNode_895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_i_913_, lean_object* v_entries_914_){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_array_get_size(v_keys_911_);
v___x_916_ = lean_nat_dec_lt(v_i_913_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_i_913_);
return v_entries_914_;
}
else
{
lean_object* v_k_917_; lean_object* v_v_918_; uint64_t v___x_919_; size_t v_h_920_; size_t v___x_921_; lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v_h_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_k_917_ = lean_array_fget_borrowed(v_keys_911_, v_i_913_);
v_v_918_ = lean_array_fget_borrowed(v_vals_912_, v_i_913_);
v___x_919_ = l_Lean_instHashableMVarId_hash(v_k_917_);
v_h_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = ((size_t)5ULL);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_sub(v_depth_910_, v___x_923_);
v___x_925_ = lean_usize_mul(v___x_921_, v___x_924_);
v_h_926_ = lean_usize_shift_right(v_h_920_, v___x_925_);
v___x_927_ = lean_nat_add(v_i_913_, v___x_922_);
lean_dec(v_i_913_);
lean_inc(v_v_918_);
lean_inc(v_k_917_);
v___x_928_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_entries_914_, v_h_926_, v_depth_910_, v_k_917_, v_v_918_);
v_i_913_ = v___x_927_;
v_entries_914_ = v___x_928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_i_933_, lean_object* v_entries_934_){
_start:
{
size_t v_depth_boxed_935_; lean_object* v_res_936_; 
v_depth_boxed_935_ = lean_unbox_usize(v_depth_930_);
lean_dec(v_depth_930_);
v_res_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_935_, v_keys_931_, v_vals_932_, v_i_933_, v_entries_934_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
size_t v_x_1690__boxed_942_; size_t v_x_1691__boxed_943_; lean_object* v_res_944_; 
v_x_1690__boxed_942_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_x_1691__boxed_943_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_937_, v_x_1690__boxed_942_, v_x_1691__boxed_943_, v_x_940_, v_x_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint64_t v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
v___x_948_ = l_Lean_instHashableMVarId_hash(v_x_946_);
v___x_949_ = lean_uint64_to_usize(v___x_948_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_945_, v___x_949_, v___x_950_, v_x_946_, v_x_947_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(lean_object* v_mvarId_952_, lean_object* v_val_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_mctx_957_; lean_object* v_cache_958_; lean_object* v_zetaDeltaFVarIds_959_; lean_object* v_postponed_960_; lean_object* v_diag_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_988_; 
v___x_956_ = lean_st_ref_take(v___y_954_);
v_mctx_957_ = lean_ctor_get(v___x_956_, 0);
v_cache_958_ = lean_ctor_get(v___x_956_, 1);
v_zetaDeltaFVarIds_959_ = lean_ctor_get(v___x_956_, 2);
v_postponed_960_ = lean_ctor_get(v___x_956_, 3);
v_diag_961_ = lean_ctor_get(v___x_956_, 4);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_988_ == 0)
{
v___x_963_ = v___x_956_;
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_diag_961_);
lean_inc(v_postponed_960_);
lean_inc(v_zetaDeltaFVarIds_959_);
lean_inc(v_cache_958_);
lean_inc(v_mctx_957_);
lean_dec(v___x_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_988_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_depth_965_; lean_object* v_levelAssignDepth_966_; lean_object* v_mvarCounter_967_; lean_object* v_lDepth_968_; lean_object* v_decls_969_; lean_object* v_userNames_970_; lean_object* v_lAssignment_971_; lean_object* v_eAssignment_972_; lean_object* v_dAssignment_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_987_; 
v_depth_965_ = lean_ctor_get(v_mctx_957_, 0);
v_levelAssignDepth_966_ = lean_ctor_get(v_mctx_957_, 1);
v_mvarCounter_967_ = lean_ctor_get(v_mctx_957_, 2);
v_lDepth_968_ = lean_ctor_get(v_mctx_957_, 3);
v_decls_969_ = lean_ctor_get(v_mctx_957_, 4);
v_userNames_970_ = lean_ctor_get(v_mctx_957_, 5);
v_lAssignment_971_ = lean_ctor_get(v_mctx_957_, 6);
v_eAssignment_972_ = lean_ctor_get(v_mctx_957_, 7);
v_dAssignment_973_ = lean_ctor_get(v_mctx_957_, 8);
v_isSharedCheck_987_ = !lean_is_exclusive(v_mctx_957_);
if (v_isSharedCheck_987_ == 0)
{
v___x_975_ = v_mctx_957_;
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_dAssignment_973_);
lean_inc(v_eAssignment_972_);
lean_inc(v_lAssignment_971_);
lean_inc(v_userNames_970_);
lean_inc(v_decls_969_);
lean_inc(v_lDepth_968_);
lean_inc(v_mvarCounter_967_);
lean_inc(v_levelAssignDepth_966_);
lean_inc(v_depth_965_);
lean_dec(v_mctx_957_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_eAssignment_972_, v_mvarId_952_, v_val_953_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 7, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_depth_965_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_levelAssignDepth_966_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_mvarCounter_967_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_lDepth_968_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_decls_969_);
lean_ctor_set(v_reuseFailAlloc_986_, 5, v_userNames_970_);
lean_ctor_set(v_reuseFailAlloc_986_, 6, v_lAssignment_971_);
lean_ctor_set(v_reuseFailAlloc_986_, 7, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 8, v_dAssignment_973_);
v___x_979_ = v_reuseFailAlloc_986_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_979_);
v___x_981_ = v___x_963_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_cache_958_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_zetaDeltaFVarIds_959_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_postponed_960_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_diag_961_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_st_ref_set(v___y_954_, v___x_981_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object* v_mvarId_989_, lean_object* v_val_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_989_, v_val_990_, v___y_991_);
lean_dec(v___y_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object* v_lhs_x27_994_, lean_object* v_h_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_997_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_997_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = l_Lean_Meta_mkEq(v_lhs_x27_994_, v_a_1008_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref(v___x_1009_);
lean_inc(v_a_1006_);
v___x_1011_ = l_Lean_MVarId_getTag(v_a_1006_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l_Lean_mkLHSGoalRaw(v_a_1010_);
v___x_1014_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1013_, v_a_1012_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_n(v_a_1015_, 2);
lean_dec_ref(v___x_1014_);
v___x_1016_ = l_Lean_Meta_mkEqTrans(v_h_995_, v_a_1015_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_a_1006_, v_a_1017_, v_a_1001_);
lean_dec_ref(v___x_1018_);
v___x_1019_ = l_Lean_Expr_mvarId_x21(v_a_1015_);
lean_dec(v_a_1015_);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1021_, v_a_997_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1022_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1015_);
lean_dec(v_a_1006_);
v_a_1023_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1016_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1016_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_a_1006_);
lean_dec_ref(v_h_995_);
v_a_1031_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1014_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1014_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1010_);
lean_dec(v_a_1006_);
lean_dec_ref(v_h_995_);
v_a_1039_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1011_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1011_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_1006_);
lean_dec_ref(v_h_995_);
v_a_1047_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1009_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1009_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1006_);
lean_dec_ref(v_h_995_);
lean_dec_ref(v_lhs_x27_994_);
v_a_1055_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1007_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1007_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_h_995_);
lean_dec_ref(v_lhs_x27_994_);
v_a_1063_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1005_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1005_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object* v_lhs_x27_1071_, lean_object* v_h_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_lhs_x27_1071_, v_h_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object* v_mvarId_1083_, lean_object* v_val_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_1083_, v_val_1084_, v___y_1090_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object* v_mvarId_1095_, lean_object* v_val_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(v_mvarId_1095_, v_val_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, size_t v_x_1114_, size_t v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_1113_, v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
size_t v_x_2084__boxed_1125_; size_t v_x_2085__boxed_1126_; lean_object* v_res_1127_; 
v_x_2084__boxed_1125_ = lean_unbox_usize(v_x_1121_);
lean_dec(v_x_1121_);
v_x_2085__boxed_1126_ = lean_unbox_usize(v_x_1122_);
lean_dec(v_x_1122_);
v_res_1127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(v_00_u03b2_1119_, v_x_1120_, v_x_2084__boxed_1125_, v_x_2085__boxed_1126_, v_x_1123_, v_x_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1128_, lean_object* v_n_1129_, lean_object* v_k_1130_, lean_object* v_v_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1129_, v_k_1130_, v_v_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1133_, size_t v_depth_1134_, lean_object* v_keys_1135_, lean_object* v_vals_1136_, lean_object* v_heq_1137_, lean_object* v_i_1138_, lean_object* v_entries_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1134_, v_keys_1135_, v_vals_1136_, v_i_1138_, v_entries_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1141_, lean_object* v_depth_1142_, lean_object* v_keys_1143_, lean_object* v_vals_1144_, lean_object* v_heq_1145_, lean_object* v_i_1146_, lean_object* v_entries_1147_){
_start:
{
size_t v_depth_boxed_1148_; lean_object* v_res_1149_; 
v_depth_boxed_1148_ = lean_unbox_usize(v_depth_1142_);
lean_dec(v_depth_1142_);
v_res_1149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1141_, v_depth_boxed_1148_, v_keys_1143_, v_vals_1144_, v_heq_1145_, v_i_1146_, v_entries_1147_);
lean_dec_ref(v_vals_1144_);
lean_dec_ref(v_keys_1143_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1151_, v_x_1152_, v_x_1153_, v_x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object* v_lhs_x27_1156_, lean_object* v_a_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1159_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1167_);
v___x_1169_ = l_Lean_Meta_mkEq(v_lhs_x27_1156_, v_a_1157_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_Lean_mkLHSGoalRaw(v_a_1170_);
v___x_1172_ = l_Lean_MVarId_replaceTargetDefEq(v_a_1168_, v___x_1171_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1175_, v___y_1159_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1176_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1172_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1172_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1168_);
v_a_1185_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1169_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1169_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_a_1157_);
lean_dec_ref(v_lhs_x27_1156_);
v_a_1193_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1167_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1167_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object* v_lhs_x27_1201_, lean_object* v_a_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(v_lhs_x27_1201_, v_a_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object* v_lhs_x27_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_1215_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___x_1223_);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1225_, 0, v_lhs_x27_1213_);
lean_closure_set(v___f_1225_, 1, v_a_1224_);
v___x_1226_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1225_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
return v___x_1226_;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v_lhs_x27_1213_);
v_a_1227_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1223_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1223_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object* v_lhs_x27_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_lhs_x27_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1247_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1255_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
v___x_1257_ = lean_whnf(v_a_1256_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1258_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v___x_1259_;
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
v_a_1260_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1257_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1257_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
v_a_1268_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1255_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1255_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___f_1296_; lean_object* v___x_1297_; 
v___f_1296_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0));
v___x_1297_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1296_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object* v_x_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object* v_x_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_Tactic_Conv_evalWhnf(v_x_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_x_1319_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1350_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5));
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___boxed), 10, 0);
v___x_1354_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1350_, v___x_1351_, v___x_1352_, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3(){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6));
v___x_1385_ = l_Lean_addBuiltinDeclarationRanges(v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1389_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = 1;
v___x_1400_ = l_Lean_Meta_reduce(v_a_1398_, v___x_1399_, v___x_1399_, v___x_1399_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1401_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1402_;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1400_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1400_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1397_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1397_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___f_1439_; lean_object* v___x_1440_; 
v___f_1439_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0));
v___x_1440_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1439_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object* v_x_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object* v_x_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Elab_Tactic_Conv_evalReduce(v_x_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_x_1462_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1488_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1));
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1491_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___boxed), 10, 0);
v___x_1492_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1488_, v___x_1489_, v___x_1490_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3(){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1522_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6));
v___x_1523_ = l_Lean_addBuiltinDeclarationRanges(v___x_1521_, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1527_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = 1;
v___x_1538_ = l_Lean_Meta_zetaReduce(v_a_1536_, v___x_1537_, v___x_1537_, v___x_1537_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1539_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1540_;
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1538_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1535_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1535_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___f_1577_; lean_object* v___x_1578_; 
v___f_1577_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0));
v___x_1578_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1577_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object* v_x_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object* v_x_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Elab_Tactic_Conv_evalZeta(v_x_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_x_1600_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1626_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1627_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1));
v___x_1628_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___boxed), 10, 0);
v___x_1630_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1626_, v___x_1627_, v___x_1628_, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3(){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1660_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6));
v___x_1661_ = l_Lean_addBuiltinDeclarationRanges(v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object* v_mvarId_1664_, lean_object* v_fvarId_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1671_; 
lean_inc(v_mvarId_1664_);
v___x_1671_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1664_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v_fst_1673_; lean_object* v_snd_1674_; uint8_t v___x_1675_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v_fst_1673_ = lean_ctor_get(v_a_1672_, 0);
lean_inc(v_fst_1673_);
v_snd_1674_ = lean_ctor_get(v_a_1672_, 1);
lean_inc(v_snd_1674_);
lean_dec(v_a_1672_);
v___x_1675_ = l_Lean_Expr_isMVar(v_snd_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_dec(v_snd_1674_);
lean_dec(v_fst_1673_);
v___x_1676_ = l_Lean_MVarId_clear(v_mvarId_1664_, v_fvarId_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Lean_Expr_mvarId_x21(v_snd_1674_);
lean_dec(v_snd_1674_);
lean_inc(v___x_1677_);
v___x_1678_ = l_Lean_MVarId_getKind(v___x_1677_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1678_);
lean_inc(v_fvarId_1665_);
v___x_1680_ = l_Lean_MVarId_clear(v___x_1677_, v_fvarId_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc_n(v_a_1681_, 2);
lean_dec_ref(v___x_1680_);
v___x_1682_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
v___x_1683_ = l_Lean_MVarId_setKind___redArg(v_a_1681_, v___x_1682_, v_a_1667_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___x_1683_);
v___x_1684_ = l_Lean_mkMVar(v_a_1681_);
v___x_1685_ = l_Lean_Meta_mkEq(v_fst_1673_, v___x_1684_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_Lean_mkLHSGoalRaw(v_a_1686_);
v___x_1688_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1664_, v___x_1687_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = l_Lean_MVarId_clear(v_a_1689_, v_fvarId_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1690_;
}
else
{
lean_dec(v_fvarId_1665_);
return v___x_1688_;
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_fvarId_1665_);
lean_dec(v_mvarId_1664_);
v_a_1691_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1685_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1685_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1681_);
lean_dec(v_fst_1673_);
lean_dec(v_fvarId_1665_);
lean_dec(v_mvarId_1664_);
v_a_1699_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1683_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1683_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_dec(v_a_1679_);
lean_dec(v_fst_1673_);
lean_dec(v_fvarId_1665_);
lean_dec(v_mvarId_1664_);
return v___x_1680_;
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___x_1677_);
lean_dec(v_fst_1673_);
lean_dec(v_fvarId_1665_);
lean_dec(v_mvarId_1664_);
v_a_1707_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1678_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1678_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
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
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_fvarId_1665_);
lean_dec(v_mvarId_1664_);
v_a_1715_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1671_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1671_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object* v_mvarId_1723_, lean_object* v_fvarId_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Elab_Tactic_Conv_convClear(v_mvarId_1723_, v_fvarId_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1730_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg(){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object* v_00_u03b1_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object* v_00_u03b1_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(v_00_u03b1_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object* v_a_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_sortFVarIds___redArg(v_a_1761_, v___y_1766_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object* v_a_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Elab_Tactic_Conv_evalClear___lam__0(v_a_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object* v_a_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1785_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = l_Lean_Elab_Tactic_Conv_convClear(v_a_1794_, v_a_1783_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1798_, v___y_1785_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1799_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1795_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1795_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_a_1783_);
v_a_1808_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1793_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1793_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object* v_a_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(v_a_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object* v_as_1827_, size_t v_sz_1828_, size_t v_i_1829_, lean_object* v_b_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_lt(v_i_1829_, v_sz_1828_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1830_);
return v___x_1841_;
}
else
{
lean_object* v_a_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_array_uget_borrowed(v_as_1827_, v_i_1829_);
lean_inc(v_a_1842_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1843_, 0, v_a_1842_);
v___x_1844_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1843_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; 
lean_dec_ref(v___x_1844_);
v___x_1845_ = lean_box(0);
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1829_, v___x_1846_);
v_i_1829_ = v___x_1847_;
v_b_1830_ = v___x_1845_;
goto _start;
}
else
{
return v___x_1844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object* v_as_1849_, lean_object* v_sz_1850_, lean_object* v_i_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
size_t v_sz_boxed_1862_; size_t v_i_boxed_1863_; lean_object* v_res_1864_; 
v_sz_boxed_1862_ = lean_unbox_usize(v_sz_1850_);
lean_dec(v_sz_1850_);
v_i_boxed_1863_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_res_1864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v_as_1849_, v_sz_boxed_1862_, v_i_boxed_1863_, v_b_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v_as_1849_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object* v_stx_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
lean_inc(v_stx_1872_);
v___x_1883_ = l_Lean_Syntax_isOfKind(v_stx_1872_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v_stx_1872_);
v___x_1884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_hs_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = l_Lean_Syntax_getArg(v_stx_1872_, v___x_1885_);
lean_dec(v_stx_1872_);
v_hs_1887_ = l_Lean_Syntax_getArgs(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = l_Lean_Elab_Tactic_getFVarIds(v_hs_1887_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1890_, 0, v_a_1889_);
v___x_1891_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1890_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; size_t v_sz_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = l_Array_reverse___redArg(v_a_1892_);
v___x_1894_ = lean_box(0);
v_sz_1895_ = lean_array_size(v___x_1893_);
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v___x_1893_, v_sz_1895_, v___x_1896_, v___x_1894_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec_ref(v___x_1893_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v___x_1897_, 0);
lean_dec(v_unused_1905_);
v___x_1899_ = v___x_1897_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_dec(v___x_1897_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1894_);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1894_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
return v___x_1897_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1891_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1891_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1888_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1888_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
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
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object* v_stx_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Elab_Tactic_Conv_evalClear(v_stx_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1(){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1941_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1942_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1));
v___x_1944_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___boxed), 10, 0);
v___x_1945_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1941_, v___x_1942_, v___x_1943_, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object* v_as_1948_, size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_a_1962_; uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1951_);
return v___x_1967_;
}
else
{
lean_object* v_next_1968_; 
v_next_1968_ = lean_ctor_get(v_b_1951_, 0);
lean_inc(v_next_1968_);
if (lean_obj_tag(v_next_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_b_1951_);
return v___x_1969_;
}
else
{
lean_object* v_upperBound_1970_; lean_object* v_val_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2014_; 
v_upperBound_1970_ = lean_ctor_get(v_b_1951_, 1);
v_val_1971_ = lean_ctor_get(v_next_1968_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_next_1968_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1973_ = v_next_1968_;
v_isShared_1974_ = v_isSharedCheck_2014_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_val_1971_);
lean_dec(v_next_1968_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2014_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_nat_dec_lt(v_val_1971_, v_upperBound_1970_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_del_object(v___x_1973_);
lean_dec(v_val_1971_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_b_1951_);
return v___x_1976_;
}
else
{
lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2011_; 
lean_inc(v_upperBound_1970_);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_b_1951_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; lean_object* v_unused_2013_; 
v_unused_2012_ = lean_ctor_get(v_b_1951_, 1);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_b_1951_, 0);
lean_dec(v_unused_2013_);
v___x_1978_ = v_b_1951_;
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_b_1951_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2011_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_a_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v_a_1980_ = lean_array_uget_borrowed(v_as_1948_, v_i_1950_);
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = lean_nat_add(v_val_1971_, v___x_1981_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1982_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_2010_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1984_);
v___x_1986_ = v___x_1978_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_upperBound_1970_);
v___x_1986_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1987_ = lean_unsigned_to_nat(2u);
v___x_1988_ = lean_nat_mod(v_val_1971_, v___x_1987_);
lean_dec(v_val_1971_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_nat_dec_eq(v___x_1988_, v___x_1989_);
lean_dec(v___x_1988_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_inc(v_a_1980_);
v___x_1991_ = l_Lean_Elab_Tactic_saveTacticInfoForToken(v_a_1980_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_dec_ref(v___x_1991_);
v_a_1962_ = v___x_1986_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v___x_1986_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_2000_; 
lean_inc(v_a_1980_);
v___x_2000_ = l_Lean_Elab_Tactic_evalTactic(v_a_1980_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref(v___x_2000_);
v_a_1962_ = v___x_1986_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v___x_1986_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
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
}
}
}
v___jp_1961_:
{
size_t v___x_1963_; size_t v___x_1964_; 
v___x_1963_ = ((size_t)1ULL);
v___x_1964_ = lean_usize_add(v_i_1950_, v___x_1963_);
v_i_1950_ = v___x_1964_;
v_b_1951_ = v_a_1962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object* v_as_2015_, lean_object* v_sz_2016_, lean_object* v_i_2017_, lean_object* v_b_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
size_t v_sz_boxed_2028_; size_t v_i_boxed_2029_; lean_object* v_res_2030_; 
v_sz_boxed_2028_ = lean_unbox_usize(v_sz_2016_);
lean_dec(v_sz_2016_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v_as_2015_, v_sz_boxed_2028_, v_i_boxed_2029_, v_b_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_as_2015_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object* v_stx_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; size_t v_sz_2047_; size_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2043_ = l_Lean_Syntax_getArgs(v_stx_2033_);
v___x_2044_ = lean_array_get_size(v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0));
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2044_);
v_sz_2047_ = lean_array_size(v___x_2043_);
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v___x_2043_, v_sz_2047_, v___x_2048_, v___x_2046_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec_ref(v___x_2043_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2049_, 0);
lean_dec(v_unused_2058_);
v___x_2051_ = v___x_2049_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v___x_2049_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_box(0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2049_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2049_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object* v_stx_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v_stx_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_stx_2067_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object* v_stx_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = l_Lean_Syntax_getArg(v_stx_2078_, v___x_2088_);
v___x_2090_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2089_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object* v_stx_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(v_stx_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_stx_2091_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2117_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_2119_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed), 10, 0);
v___x_2121_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2117_, v___x_2118_, v___x_2119_, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3(){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6));
v___x_2152_ = l_Lean_addBuiltinDeclarationRanges(v___x_2150_, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object* v_a_2155_, lean_object* v_trees_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2166_ = lean_apply_9(v_a_2155_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2175_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2167_);
lean_ctor_set(v___x_2171_, 1, v_trees_2156_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_trees_2156_);
v_a_2176_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2166_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2166_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object* v_a_2184_, lean_object* v_trees_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(v_a_2184_, v_trees_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object* v___x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2196_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object* v___x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(v___x_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object* v___y_2218_, lean_object* v_mkInfoTree_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v_a_2227_, lean_object* v_a_x3f_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v_infoState_2231_; lean_object* v_trees_2232_; lean_object* v___x_2233_; 
v___x_2230_ = lean_st_ref_get(v___y_2218_);
v_infoState_2231_ = lean_ctor_get(v___x_2230_, 7);
lean_inc_ref(v_infoState_2231_);
lean_dec(v___x_2230_);
v_trees_2232_ = lean_ctor_get(v_infoState_2231_, 2);
lean_inc_ref(v_trees_2232_);
lean_dec_ref(v_infoState_2231_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2222_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
v___x_2233_ = lean_apply_10(v_mkInfoTree_2219_, v_trees_2232_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2218_, lean_box(0));
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2272_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2272_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2272_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v_infoState_2239_; lean_object* v_env_2240_; lean_object* v_nextMacroScope_2241_; lean_object* v_ngen_2242_; lean_object* v_auxDeclNGen_2243_; lean_object* v_traceState_2244_; lean_object* v_cache_2245_; lean_object* v_messages_2246_; lean_object* v_snapshotTasks_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2271_; 
v___x_2238_ = lean_st_ref_take(v___y_2218_);
v_infoState_2239_ = lean_ctor_get(v___x_2238_, 7);
v_env_2240_ = lean_ctor_get(v___x_2238_, 0);
v_nextMacroScope_2241_ = lean_ctor_get(v___x_2238_, 1);
v_ngen_2242_ = lean_ctor_get(v___x_2238_, 2);
v_auxDeclNGen_2243_ = lean_ctor_get(v___x_2238_, 3);
v_traceState_2244_ = lean_ctor_get(v___x_2238_, 4);
v_cache_2245_ = lean_ctor_get(v___x_2238_, 5);
v_messages_2246_ = lean_ctor_get(v___x_2238_, 6);
v_snapshotTasks_2247_ = lean_ctor_get(v___x_2238_, 8);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2271_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snapshotTasks_2247_);
lean_inc(v_infoState_2239_);
lean_inc(v_messages_2246_);
lean_inc(v_cache_2245_);
lean_inc(v_traceState_2244_);
lean_inc(v_auxDeclNGen_2243_);
lean_inc(v_ngen_2242_);
lean_inc(v_nextMacroScope_2241_);
lean_inc(v_env_2240_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2271_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
uint8_t v_enabled_2251_; lean_object* v_assignment_2252_; lean_object* v_lazyAssignment_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2269_; 
v_enabled_2251_ = lean_ctor_get_uint8(v_infoState_2239_, sizeof(void*)*3);
v_assignment_2252_ = lean_ctor_get(v_infoState_2239_, 0);
v_lazyAssignment_2253_ = lean_ctor_get(v_infoState_2239_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_infoState_2239_);
if (v_isSharedCheck_2269_ == 0)
{
lean_object* v_unused_2270_; 
v_unused_2270_ = lean_ctor_get(v_infoState_2239_, 2);
lean_dec(v_unused_2270_);
v___x_2255_ = v_infoState_2239_;
v_isShared_2256_ = v_isSharedCheck_2269_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_lazyAssignment_2253_);
lean_inc(v_assignment_2252_);
lean_dec(v_infoState_2239_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2269_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = l_Lean_PersistentArray_push___redArg(v_a_2227_, v_a_2234_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 2, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_assignment_2252_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_lazyAssignment_2253_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v___x_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*3, v_enabled_2251_);
v___x_2259_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2261_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 7, v___x_2259_);
v___x_2261_ = v___x_2249_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_env_2240_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_nextMacroScope_2241_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_ngen_2242_);
lean_ctor_set(v_reuseFailAlloc_2267_, 3, v_auxDeclNGen_2243_);
lean_ctor_set(v_reuseFailAlloc_2267_, 4, v_traceState_2244_);
lean_ctor_set(v_reuseFailAlloc_2267_, 5, v_cache_2245_);
lean_ctor_set(v_reuseFailAlloc_2267_, 6, v_messages_2246_);
lean_ctor_set(v_reuseFailAlloc_2267_, 7, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 8, v_snapshotTasks_2247_);
v___x_2261_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = lean_st_ref_set(v___y_2218_, v___x_2261_);
v___x_2263_ = lean_box(0);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2263_);
v___x_2265_ = v___x_2236_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_a_2227_);
v_a_2273_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2233_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2233_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(lean_object* v___y_2281_, lean_object* v_mkInfoTree_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v_a_2290_, lean_object* v_a_x3f_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2281_, v_mkInfoTree_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v_a_2290_, v_a_x3f_2291_);
lean_dec(v_a_x3f_2291_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2281_);
return v_res_2293_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_unsigned_to_nat(32u);
v___x_2295_ = lean_mk_empty_array_with_capacity(v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = ((size_t)5ULL);
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_unsigned_to_nat(32u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0);
v___x_2302_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2300_);
lean_ctor_set(v___x_2302_, 2, v___x_2298_);
lean_ctor_set(v___x_2302_, 3, v___x_2298_);
lean_ctor_set_usize(v___x_2302_, 4, v___x_2297_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v_infoState_2306_; lean_object* v_trees_2307_; lean_object* v___x_2308_; lean_object* v_infoState_2309_; lean_object* v_env_2310_; lean_object* v_nextMacroScope_2311_; lean_object* v_ngen_2312_; lean_object* v_auxDeclNGen_2313_; lean_object* v_traceState_2314_; lean_object* v_cache_2315_; lean_object* v_messages_2316_; lean_object* v_snapshotTasks_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2338_; 
v___x_2305_ = lean_st_ref_get(v___y_2303_);
v_infoState_2306_ = lean_ctor_get(v___x_2305_, 7);
lean_inc_ref(v_infoState_2306_);
lean_dec(v___x_2305_);
v_trees_2307_ = lean_ctor_get(v_infoState_2306_, 2);
lean_inc_ref(v_trees_2307_);
lean_dec_ref(v_infoState_2306_);
v___x_2308_ = lean_st_ref_take(v___y_2303_);
v_infoState_2309_ = lean_ctor_get(v___x_2308_, 7);
v_env_2310_ = lean_ctor_get(v___x_2308_, 0);
v_nextMacroScope_2311_ = lean_ctor_get(v___x_2308_, 1);
v_ngen_2312_ = lean_ctor_get(v___x_2308_, 2);
v_auxDeclNGen_2313_ = lean_ctor_get(v___x_2308_, 3);
v_traceState_2314_ = lean_ctor_get(v___x_2308_, 4);
v_cache_2315_ = lean_ctor_get(v___x_2308_, 5);
v_messages_2316_ = lean_ctor_get(v___x_2308_, 6);
v_snapshotTasks_2317_ = lean_ctor_get(v___x_2308_, 8);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2319_ = v___x_2308_;
v_isShared_2320_ = v_isSharedCheck_2338_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_snapshotTasks_2317_);
lean_inc(v_infoState_2309_);
lean_inc(v_messages_2316_);
lean_inc(v_cache_2315_);
lean_inc(v_traceState_2314_);
lean_inc(v_auxDeclNGen_2313_);
lean_inc(v_ngen_2312_);
lean_inc(v_nextMacroScope_2311_);
lean_inc(v_env_2310_);
lean_dec(v___x_2308_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2338_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint8_t v_enabled_2321_; lean_object* v_assignment_2322_; lean_object* v_lazyAssignment_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2336_; 
v_enabled_2321_ = lean_ctor_get_uint8(v_infoState_2309_, sizeof(void*)*3);
v_assignment_2322_ = lean_ctor_get(v_infoState_2309_, 0);
v_lazyAssignment_2323_ = lean_ctor_get(v_infoState_2309_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_infoState_2309_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v_infoState_2309_, 2);
lean_dec(v_unused_2337_);
v___x_2325_ = v_infoState_2309_;
v_isShared_2326_ = v_isSharedCheck_2336_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_lazyAssignment_2323_);
lean_inc(v_assignment_2322_);
lean_dec(v_infoState_2309_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2336_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 2, v___x_2327_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_assignment_2322_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_lazyAssignment_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v___x_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*3, v_enabled_2321_);
v___x_2329_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 7, v___x_2329_);
v___x_2331_ = v___x_2319_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_env_2310_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_nextMacroScope_2311_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_ngen_2312_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_auxDeclNGen_2313_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_traceState_2314_);
lean_ctor_set(v_reuseFailAlloc_2334_, 5, v_cache_2315_);
lean_ctor_set(v_reuseFailAlloc_2334_, 6, v_messages_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 7, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2334_, 8, v_snapshotTasks_2317_);
v___x_2331_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_st_ref_set(v___y_2303_, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_trees_2307_);
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2339_);
lean_dec(v___y_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object* v_x_2342_, lean_object* v_mkInfoTree_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v_infoState_2354_; uint8_t v_enabled_2355_; 
v___x_2353_ = lean_st_ref_get(v___y_2351_);
v_infoState_2354_ = lean_ctor_get(v___x_2353_, 7);
lean_inc_ref(v_infoState_2354_);
lean_dec(v___x_2353_);
v_enabled_2355_ = lean_ctor_get_uint8(v_infoState_2354_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2354_);
if (v_enabled_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec_ref(v_mkInfoTree_2343_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
v___x_2356_ = lean_apply_9(v_x_2342_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v_r_2359_; 
v___x_2357_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2351_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
v_r_2359_ = lean_apply_9(v_x_2342_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v_r_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2384_; 
v_a_2360_ = lean_ctor_get(v_r_2359_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_r_2359_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2362_ = v_r_2359_;
v_isShared_2363_ = v_isSharedCheck_2384_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v_r_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2384_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
lean_inc(v_a_2360_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 1);
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2351_, v_mkInfoTree_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v_a_2358_, v___x_2365_);
lean_dec_ref(v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2374_);
v___x_2368_ = v___x_2366_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_dec(v___x_2366_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v_a_2360_);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2360_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2360_);
v_a_2375_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v_r_2359_, 0);
lean_inc(v_a_2385_);
lean_dec_ref(v_r_2359_);
v___x_2386_ = lean_box(0);
v___x_2387_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2351_, v_mkInfoTree_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v_a_2358_, v___x_2386_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v___x_2387_, 0);
lean_dec(v_unused_2395_);
v___x_2389_ = v___x_2387_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_dec(v___x_2387_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 1);
lean_ctor_set(v___x_2389_, 0, v_a_2385_);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2385_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2385_);
v_a_2396_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2387_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2387_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object* v_x_2404_, lean_object* v_mkInfoTree_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2404_, v_mkInfoTree_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object* v___f_2467_, lean_object* v___f_2468_, lean_object* v_stx_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___f_2467_, v___f_2468_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec_ref(v___x_2479_);
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = l_Lean_Syntax_getArg(v_stx_2469_, v___x_2480_);
v___x_2482_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2481_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_ref_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref(v___x_2482_);
v_ref_2483_ = lean_ctor_get(v___y_2476_, 5);
v___x_2484_ = 0;
v___x_2485_ = l_Lean_SourceInfo_fromRef(v_ref_2483_, v___x_2484_);
v___x_2486_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1));
v___x_2487_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2));
lean_inc_n(v___x_2485_, 22);
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_2490_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_2491_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_2492_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10));
v___x_2493_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_2494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2485_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_2496_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2485_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_2499_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
v___x_2500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2485_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_2503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2485_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2501_, v___x_2503_);
v___x_2505_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2491_, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2490_, v___x_2505_);
v___x_2507_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2489_, v___x_2506_);
v___x_2508_ = l_Lean_Syntax_node2(v___x_2485_, v___x_2498_, v___x_2500_, v___x_2507_);
v___x_2509_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2491_, v___x_2508_);
v___x_2510_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2490_, v___x_2509_);
v___x_2511_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2489_, v___x_2510_);
v___x_2512_ = l_Lean_Syntax_node2(v___x_2485_, v___x_2495_, v___x_2497_, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2491_, v___x_2512_);
v___x_2514_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2490_, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2489_, v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_2517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2485_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = l_Lean_Syntax_node3(v___x_2485_, v___x_2492_, v___x_2494_, v___x_2515_, v___x_2517_);
v___x_2519_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2491_, v___x_2518_);
v___x_2520_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2490_, v___x_2519_);
v___x_2521_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2489_, v___x_2520_);
v___x_2522_ = l_Lean_Syntax_node2(v___x_2485_, v___x_2486_, v___x_2488_, v___x_2521_);
v___x_2523_ = l_Lean_Elab_Tactic_evalTactic(v___x_2522_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2523_;
}
else
{
return v___x_2482_;
}
}
else
{
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object* v___f_2524_, lean_object* v___f_2525_, lean_object* v_stx_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(v___f_2524_, v___f_2525_, v_stx_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v_stx_2526_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object* v_stx_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = l_Lean_Syntax_getArg(v_stx_2539_, v___x_2549_);
v___x_2551_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2550_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v_fileName_2553_; lean_object* v_fileMap_2554_; lean_object* v_options_2555_; lean_object* v_currRecDepth_2556_; lean_object* v_maxRecDepth_2557_; lean_object* v_ref_2558_; lean_object* v_currNamespace_2559_; lean_object* v_openDecls_2560_; lean_object* v_initHeartbeats_2561_; lean_object* v_maxHeartbeats_2562_; lean_object* v_quotContext_2563_; lean_object* v_currMacroScope_2564_; uint8_t v_diag_2565_; lean_object* v_cancelTk_x3f_2566_; uint8_t v_suppressElabErrors_2567_; lean_object* v_inheritedTraceOptions_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v_ref_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v_fileName_2553_ = lean_ctor_get(v_a_2546_, 0);
v_fileMap_2554_ = lean_ctor_get(v_a_2546_, 1);
v_options_2555_ = lean_ctor_get(v_a_2546_, 2);
v_currRecDepth_2556_ = lean_ctor_get(v_a_2546_, 3);
v_maxRecDepth_2557_ = lean_ctor_get(v_a_2546_, 4);
v_ref_2558_ = lean_ctor_get(v_a_2546_, 5);
v_currNamespace_2559_ = lean_ctor_get(v_a_2546_, 6);
v_openDecls_2560_ = lean_ctor_get(v_a_2546_, 7);
v_initHeartbeats_2561_ = lean_ctor_get(v_a_2546_, 8);
v_maxHeartbeats_2562_ = lean_ctor_get(v_a_2546_, 9);
v_quotContext_2563_ = lean_ctor_get(v_a_2546_, 10);
v_currMacroScope_2564_ = lean_ctor_get(v_a_2546_, 11);
v_diag_2565_ = lean_ctor_get_uint8(v_a_2546_, sizeof(void*)*14);
v_cancelTk_x3f_2566_ = lean_ctor_get(v_a_2546_, 12);
v_suppressElabErrors_2567_ = lean_ctor_get_uint8(v_a_2546_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2568_ = lean_ctor_get(v_a_2546_, 13);
v___f_2569_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2569_, 0, v_a_2552_);
v___x_2570_ = lean_unsigned_to_nat(2u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_2539_, v___x_2570_);
v___f_2572_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0));
v___f_2573_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2573_, 0, v___f_2572_);
lean_closure_set(v___f_2573_, 1, v___f_2569_);
lean_closure_set(v___f_2573_, 2, v_stx_2539_);
v_ref_2574_ = l_Lean_replaceRef(v___x_2571_, v_ref_2558_);
lean_dec(v___x_2571_);
lean_inc_ref(v_inheritedTraceOptions_2568_);
lean_inc(v_cancelTk_x3f_2566_);
lean_inc(v_currMacroScope_2564_);
lean_inc(v_quotContext_2563_);
lean_inc(v_maxHeartbeats_2562_);
lean_inc(v_initHeartbeats_2561_);
lean_inc(v_openDecls_2560_);
lean_inc(v_currNamespace_2559_);
lean_inc(v_maxRecDepth_2557_);
lean_inc(v_currRecDepth_2556_);
lean_inc_ref(v_options_2555_);
lean_inc_ref(v_fileMap_2554_);
lean_inc_ref(v_fileName_2553_);
v___x_2575_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2575_, 0, v_fileName_2553_);
lean_ctor_set(v___x_2575_, 1, v_fileMap_2554_);
lean_ctor_set(v___x_2575_, 2, v_options_2555_);
lean_ctor_set(v___x_2575_, 3, v_currRecDepth_2556_);
lean_ctor_set(v___x_2575_, 4, v_maxRecDepth_2557_);
lean_ctor_set(v___x_2575_, 5, v_ref_2574_);
lean_ctor_set(v___x_2575_, 6, v_currNamespace_2559_);
lean_ctor_set(v___x_2575_, 7, v_openDecls_2560_);
lean_ctor_set(v___x_2575_, 8, v_initHeartbeats_2561_);
lean_ctor_set(v___x_2575_, 9, v_maxHeartbeats_2562_);
lean_ctor_set(v___x_2575_, 10, v_quotContext_2563_);
lean_ctor_set(v___x_2575_, 11, v_currMacroScope_2564_);
lean_ctor_set(v___x_2575_, 12, v_cancelTk_x3f_2566_);
lean_ctor_set(v___x_2575_, 13, v_inheritedTraceOptions_2568_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*14, v_diag_2565_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*14 + 1, v_suppressElabErrors_2567_);
v___x_2576_ = l_Lean_Elab_Tactic_closeUsingOrAdmit(v___f_2573_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v___x_2575_, v_a_2547_);
lean_dec_ref(v___x_2575_);
return v___x_2576_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_stx_2539_);
v_a_2577_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2551_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2551_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object* v_stx_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v_stx_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object* v_00_u03b1_2616_, lean_object* v_x_2617_, lean_object* v_mkInfoTree_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2617_, v_mkInfoTree_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object* v_00_u03b1_2629_, lean_object* v_x_2630_, lean_object* v_mkInfoTree_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(v_00_u03b1_2629_, v_x_2630_, v_mkInfoTree_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2657_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1));
v___x_2659_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2660_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed), 10, 0);
v___x_2661_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2657_, v___x_2658_, v___x_2659_, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3(){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6));
v___x_2692_ = l_Lean_addBuiltinDeclarationRanges(v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object* v_stx_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = l_Lean_Syntax_getArg(v_stx_2695_, v___x_2705_);
v___x_2707_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v___x_2706_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object* v_stx_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Elab_Tactic_Conv_evalNestedConv(v_stx_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_stx_2708_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2734_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1));
v___x_2736_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2737_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed), 10, 0);
v___x_2738_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2734_, v___x_2735_, v___x_2736_, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3(){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2768_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6));
v___x_2769_ = l_Lean_addBuiltinDeclarationRanges(v___x_2767_, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object* v_stx_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = l_Lean_Syntax_getArg(v_stx_2772_, v___x_2782_);
v___x_2784_ = l_Lean_Elab_Tactic_evalTactic(v___x_2783_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object* v_stx_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Elab_Tactic_Conv_evalConvSeq(v_stx_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_stx_2785_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2811_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2812_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2814_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed), 10, 0);
v___x_2815_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2811_, v___x_2812_, v___x_2813_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3(){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6));
v___x_2846_ = l_Lean_addBuiltinDeclarationRanges(v___x_2844_, v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object* v_stx_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_2851_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = lean_unsigned_to_nat(2u);
v___x_2862_ = l_Lean_Syntax_getArg(v_stx_2849_, v___x_2861_);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = l_Lean_Syntax_getArg(v___x_2862_, v___x_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_2865_, 0, v___x_2864_);
v___x_2866_ = l_Lean_Elab_Tactic_Conv_convert(v_a_2860_, v___x_2865_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v___x_2870_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v_fst_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_fst_2868_);
v_snd_2869_ = lean_ctor_get(v_a_2867_, 1);
lean_inc(v_snd_2869_);
lean_dec(v_a_2867_);
v___x_2870_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_fst_2868_, v_snd_2869_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
return v___x_2870_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_a_2871_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2866_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2866_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_a_2879_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2859_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2859_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object* v_stx_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(v_stx_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v_stx_2887_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object* v_stx_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___f_2908_; lean_object* v___x_2909_; 
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2908_, 0, v_stx_2898_);
v___x_2909_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2908_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object* v_stx_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq(v_stx_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2936_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2937_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1));
v___x_2938_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_2939_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed), 10, 0);
v___x_2940_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2936_, v___x_2937_, v___x_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3(){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_2970_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6));
v___x_2971_ = l_Lean_addBuiltinDeclarationRanges(v___x_2969_, v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object* v_stx_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = l_Lean_Syntax_getArg(v_stx_2974_, v___x_2984_);
v___x_2986_ = l_Lean_Elab_Tactic_evalTactic(v___x_2985_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object* v_stx_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Elab_Tactic_Conv_evalParen(v_stx_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_stx_2987_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3012_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3013_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3015_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalParen___boxed), 10, 0);
v___x_3016_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3012_, v___x_3013_, v___x_3014_, v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3(){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3046_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6));
v___x_3047_ = l_Lean_addBuiltinDeclarationRanges(v___x_3045_, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
v___x_3060_ = lean_apply_9(v_x_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, lean_box(0));
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(v_x_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object* v_mvarId_3072_, lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___f_3083_; lean_object* v___x_3084_; 
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
v___f_3083_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3083_, 0, v_x_3073_);
lean_closure_set(v___f_3083_, 1, v___y_3074_);
lean_closure_set(v___f_3083_, 2, v___y_3075_);
lean_closure_set(v___f_3083_, 3, v___y_3076_);
lean_closure_set(v___f_3083_, 4, v___y_3077_);
v___x_3084_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3072_, v___f_3083_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3084_) == 0)
{
return v___x_3084_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object* v_00_u03b1_3105_, lean_object* v_mvarId_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_mvarId_3119_, lean_object* v_x_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(v_00_u03b1_3118_, v_mvarId_3119_, v_x_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object* v_head_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
lean_inc(v_head_3131_);
v___x_3141_ = l_Lean_MVarId_getType(v_head_3131_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_n(v_a_3142_, 2);
lean_dec_ref(v___x_3141_);
v___x_3143_ = l_Lean_Meta_matchEq_x3f(v_a_3142_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3170_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3170_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3170_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
if (lean_obj_tag(v_a_3144_) == 1)
{
lean_object* v_val_3148_; lean_object* v_snd_3149_; lean_object* v_snd_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_val_3148_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_val_3148_);
lean_dec_ref(v_a_3144_);
v_snd_3149_ = lean_ctor_get(v_val_3148_, 1);
lean_inc(v_snd_3149_);
lean_dec(v_val_3148_);
v_snd_3150_ = lean_ctor_get(v_snd_3149_, 1);
lean_inc(v_snd_3150_);
lean_dec(v_snd_3149_);
v___x_3151_ = l_Lean_Expr_getAppFn(v_snd_3150_);
lean_dec(v_snd_3150_);
v___x_3152_ = l_Lean_Expr_isMVar(v___x_3151_);
lean_dec_ref(v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3154_; 
lean_dec(v_a_3142_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v_head_3131_);
v___x_3154_ = v___x_3146_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_head_3131_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
else
{
lean_object* v___x_3156_; 
lean_del_object(v___x_3146_);
v___x_3156_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_3142_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = l_Lean_MVarId_replaceTargetDefEq(v_head_3131_, v_a_3157_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3158_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_head_3131_);
v_a_3159_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3156_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3156_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
else
{
lean_object* v___x_3168_; 
lean_dec(v_a_3144_);
lean_dec(v_a_3142_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v_head_3131_);
v___x_3168_ = v___x_3146_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_head_3131_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3142_);
lean_dec(v_head_3131_);
v_a_3171_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3143_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3143_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_head_3131_);
v_a_3179_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3141_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3141_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object* v_head_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(v_head_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object* v_x_3198_, lean_object* v_x_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = l_List_reverse___redArg(v_x_3199_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
else
{
lean_object* v_head_3211_; lean_object* v_tail_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3231_; 
v_head_3211_ = lean_ctor_get(v_x_3198_, 0);
v_tail_3212_ = lean_ctor_get(v_x_3198_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_x_3198_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3214_ = v_x_3198_;
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_tail_3212_);
lean_inc(v_head_3211_);
lean_dec(v_x_3198_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; 
lean_inc(v_head_3211_);
v___f_3216_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3216_, 0, v_head_3211_);
v___x_3217_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_head_3211_, v___f_3216_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v_x_3199_);
lean_ctor_set(v___x_3214_, 0, v_a_3218_);
v___x_3220_ = v___x_3214_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3218_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_x_3199_);
v___x_3220_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
v_x_3198_ = v_tail_3212_;
v_x_3199_ = v___x_3220_;
goto _start;
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_del_object(v___x_3214_);
lean_dec(v_tail_3212_);
lean_dec(v_x_3199_);
v_a_3223_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3217_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3217_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_x_3232_, v_x_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = lean_box(0);
v___x_3256_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_a_3254_, v___x_3255_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_3257_, v_a_3245_);
return v___x_3258_;
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
v_a_3259_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3256_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3256_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
v_a_3267_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3253_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3253_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object* v_stx_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v_seq_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_unsigned_to_nat(2u);
v_seq_3296_ = l_Lean_Syntax_getArg(v_stx_3285_, v___x_3295_);
v___x_3297_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3296_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v___x_3298_; 
lean_dec_ref(v___x_3297_);
v___x_3298_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3298_;
}
else
{
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object* v_stx_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(v_stx_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_stx_3299_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3325_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3326_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1));
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3328_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed), 10, 0);
v___x_3329_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3325_, v___x_3326_, v___x_3327_, v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3(){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6));
v___x_3360_ = l_Lean_addBuiltinDeclarationRanges(v___x_3358_, v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object* v_seq_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v___x_3374_; 
lean_dec_ref(v___x_3373_);
v___x_3374_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
return v___x_3374_;
}
else
{
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object* v_seq_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(v_seq_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object* v_a_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = l_Lean_Expr_mdataExpr_x21(v_a_3386_);
v___x_3399_ = l_Lean_MVarId_replaceTargetDefEq(v_a_3397_, v___x_3398_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_a_3400_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3402_, v___y_3388_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3403_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
v_a_3404_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3399_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3399_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_a_3412_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3396_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3396_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object* v_a_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_a_3420_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object* v_stx_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Elab_Tactic_getMainTarget(v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; lean_object* v_seq_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = lean_unsigned_to_nat(2u);
v_seq_3444_ = l_Lean_Syntax_getArg(v_stx_3431_, v___x_3443_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3445_, 0, v_seq_3444_);
v___x_3446_ = l_Lean_isLHSGoal_x3f(v_a_3442_);
if (lean_obj_tag(v___x_3446_) == 1)
{
lean_object* v___f_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v___x_3446_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3447_, 0, v_a_3442_);
v___x_3448_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3447_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v___x_3449_; 
lean_dec_ref(v___x_3448_);
v___x_3449_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3445_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3449_;
}
else
{
lean_dec_ref(v___f_3445_);
return v___x_3448_;
}
}
else
{
lean_object* v___x_3450_; 
lean_dec(v___x_3446_);
lean_dec(v_a_3442_);
v___x_3450_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3445_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3450_;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_a_3451_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3441_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3441_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object* v_stx_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic(v_stx_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_stx_3459_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3485_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3486_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1));
v___x_3487_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3488_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed), 10, 0);
v___x_3489_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3485_, v___x_3486_, v___x_3487_, v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3(){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3519_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6));
v___x_3520_ = l_Lean_addBuiltinDeclarationRanges(v___x_3518_, v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object* v_stx_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = lean_unsigned_to_nat(2u);
v___x_3534_ = l_Lean_Syntax_getArg(v_stx_3523_, v___x_3533_);
v___x_3535_ = l_Lean_Elab_Tactic_evalTactic(v___x_3534_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object* v_stx_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_Elab_Tactic_Conv_evalConvTactic(v_stx_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_stx_3536_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3562_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3563_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1));
v___x_3564_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3565_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed), 10, 0);
v___x_3566_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3562_, v___x_3563_, v___x_3564_, v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3(){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3596_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6));
v___x_3597_ = l_Lean_addBuiltinDeclarationRanges(v___x_3595_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object* v_ref_3600_, lean_object* v___x_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_3600_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___f_3613_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3613_, 0, v_a_3612_);
v___x_3614_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___x_3601_, v___f_3613_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v___x_3614_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v___x_3601_);
v_a_3615_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3611_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3611_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object* v_ref_3623_, lean_object* v___x_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(v_ref_3623_, v___x_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object* v_fst_3635_, lean_object* v_snd_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3638_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref(v___x_3646_);
v___x_3648_ = l_Lean_MVarId_replaceTargetEq(v_a_3647_, v_fst_3635_, v_snd_3636_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3651_, 0, v_a_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3651_, v___y_3638_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3652_;
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3648_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3648_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v_snd_3636_);
lean_dec_ref(v_fst_3635_);
v_a_3661_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3646_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3646_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object* v_fst_3669_, lean_object* v_snd_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(v_fst_3669_, v_snd_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object* v_conv_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Elab_Tactic_getMainTarget(v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v_ref_3693_; lean_object* v___x_3694_; lean_object* v___f_3695_; lean_object* v___x_3696_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref(v___x_3691_);
v_ref_3693_ = lean_ctor_get(v___y_3688_, 5);
v___x_3694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3694_, 0, v_conv_3681_);
lean_inc(v_ref_3693_);
v___f_3695_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3695_, 0, v_ref_3693_);
lean_closure_set(v___f_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_Elab_Tactic_Conv_convert(v_a_3692_, v___f_3695_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v_fst_3698_; lean_object* v_snd_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3731_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3696_);
v_fst_3698_ = lean_ctor_get(v_a_3697_, 0);
v_snd_3699_ = lean_ctor_get(v_a_3697_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_a_3697_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3701_ = v_a_3697_;
v_isShared_3702_ = v_isSharedCheck_3731_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_snd_3699_);
lean_inc(v_fst_3698_);
lean_dec(v_a_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3731_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___f_3703_; lean_object* v___x_3704_; 
v___f_3703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3703_, 0, v_fst_3698_);
lean_closure_set(v___f_3703_, 1, v_snd_3699_);
v___x_3704_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3703_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3704_) == 0)
{
uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec_ref(v___x_3704_);
v___x_3705_ = 0;
v___x_3706_ = l_Lean_SourceInfo_fromRef(v_ref_3693_, v___x_3705_);
v___x_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
lean_inc(v___x_3706_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set_tag(v___x_3701_, 2);
lean_ctor_set(v___x_3701_, 1, v___x_3708_);
lean_ctor_set(v___x_3701_, 0, v___x_3706_);
v___x_3710_ = v___x_3701_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3711_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_3712_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_3713_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_3714_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
lean_inc_n(v___x_3706_, 10);
v___x_3716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3706_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_3718_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_3719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3706_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3717_, v___x_3719_);
v___x_3721_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3713_, v___x_3720_);
v___x_3722_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3712_, v___x_3721_);
v___x_3723_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3711_, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node2(v___x_3706_, v___x_3714_, v___x_3716_, v___x_3723_);
v___x_3725_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3713_, v___x_3724_);
v___x_3726_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3712_, v___x_3725_);
v___x_3727_ = l_Lean_Syntax_node1(v___x_3706_, v___x_3711_, v___x_3726_);
v___x_3728_ = l_Lean_Syntax_node2(v___x_3706_, v___x_3707_, v___x_3710_, v___x_3727_);
v___x_3729_ = l_Lean_Elab_Tactic_evalTactic(v___x_3728_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec_ref(v___y_3688_);
return v___x_3729_;
}
}
else
{
lean_del_object(v___x_3701_);
lean_dec_ref(v___y_3688_);
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v___y_3688_);
v_a_3732_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3696_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3696_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v___y_3688_);
lean_dec(v_conv_3681_);
v_a_3740_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3691_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3691_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object* v_conv_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(v_conv_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object* v_conv_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___f_3769_; lean_object* v___x_3770_; 
v___f_3769_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3769_, 0, v_conv_3759_);
v___x_3770_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3769_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object* v_conv_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v_conv_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object* v_a_3782_, lean_object* v_fst_3783_, lean_object* v_snd_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3786_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = l_Lean_LocalDecl_fvarId(v_a_3782_);
v___x_3797_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_a_3795_, v___x_3796_, v_fst_3783_, v_snd_3784_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_mvarId_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3797_);
v_mvarId_3799_ = lean_ctor_get(v_a_3798_, 1);
lean_inc(v_mvarId_3799_);
lean_dec(v_a_3798_);
v___x_3800_ = lean_box(0);
v___x_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3801_, 0, v_mvarId_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3801_, v___y_3786_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3802_;
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
v_a_3803_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3797_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3797_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_snd_3784_);
lean_dec_ref(v_fst_3783_);
v_a_3811_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3794_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3794_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object* v_a_3819_, lean_object* v_fst_3820_, lean_object* v_snd_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(v_a_3819_, v_fst_3820_, v_snd_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v_a_3819_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object* v_hUserName_3832_, lean_object* v_conv_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Meta_getLocalDeclFromUserName(v_hUserName_3832_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v_ref_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3843_);
v_ref_3845_ = lean_ctor_get(v___y_3840_, 5);
v___x_3846_ = l_Lean_LocalDecl_type(v_a_3844_);
v___x_3847_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3847_, 0, v_conv_3833_);
lean_inc(v_ref_3845_);
v___f_3848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3848_, 0, v_ref_3845_);
lean_closure_set(v___f_3848_, 1, v___x_3847_);
v___x_3849_ = l_Lean_Elab_Tactic_Conv_convert(v___x_3846_, v___f_3848_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v_fst_3851_; lean_object* v_snd_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v_fst_3851_ = lean_ctor_get(v_a_3850_, 0);
lean_inc(v_fst_3851_);
v_snd_3852_ = lean_ctor_get(v_a_3850_, 1);
lean_inc(v_snd_3852_);
lean_dec(v_a_3850_);
v___f_3853_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed), 12, 3);
lean_closure_set(v___f_3853_, 0, v_a_3844_);
lean_closure_set(v___f_3853_, 1, v_fst_3851_);
lean_closure_set(v___f_3853_, 2, v_snd_3852_);
v___x_3854_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3853_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec_ref(v___y_3840_);
return v___x_3854_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3844_);
lean_dec_ref(v___y_3840_);
v_a_3855_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3849_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3849_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v___y_3840_);
lean_dec(v_conv_3833_);
v_a_3863_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3843_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3843_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object* v_hUserName_3871_, lean_object* v_conv_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(v_hUserName_3871_, v_conv_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object* v_conv_3883_, lean_object* v_hUserName_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___f_3894_; lean_object* v___x_3895_; 
v___f_3894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3894_, 0, v_hUserName_3884_);
lean_closure_set(v___f_3894_, 1, v_conv_3883_);
v___x_3895_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3894_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object* v_conv_3896_, lean_object* v_hUserName_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v_conv_3896_, v_hUserName_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
return v_res_3907_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7(void){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Array_mkArray0(lean_box(0));
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object* v_stx_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; uint8_t v___x_3979_; 
v___x_3938_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__0));
v___x_3939_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
lean_inc(v_stx_3928_);
v___x_3979_ = l_Lean_Syntax_isOfKind(v_stx_3928_, v___x_3939_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_dec(v_stx_3928_);
v___x_3980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v_tk_4015_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___x_4043_; lean_object* v_loc_x3f_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_3981_ = lean_unsigned_to_nat(0u);
v_tk_4015_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_3981_);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4107_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4043_);
v___x_4108_ = l_Lean_Syntax_isNone(v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4109_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4107_);
v___x_4110_ = l_Lean_Syntax_matchesNull(v___x_4107_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
lean_dec(v___x_4107_);
lean_dec(v_tk_4015_);
lean_dec(v_stx_3928_);
v___x_4111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4111_;
}
else
{
lean_object* v_loc_x3f_4112_; lean_object* v___x_4113_; 
v_loc_x3f_4112_ = l_Lean_Syntax_getArg(v___x_4107_, v___x_4043_);
lean_dec(v___x_4107_);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_loc_x3f_4112_);
v_loc_x3f_4045_ = v___x_4113_;
v___y_4046_ = v_a_3929_;
v___y_4047_ = v_a_3930_;
v___y_4048_ = v_a_3931_;
v___y_4049_ = v_a_3932_;
v___y_4050_ = v_a_3933_;
v___y_4051_ = v_a_3934_;
v___y_4052_ = v_a_3935_;
v___y_4053_ = v_a_3936_;
goto v___jp_4044_;
}
}
else
{
lean_object* v___x_4114_; 
lean_dec(v___x_4107_);
v___x_4114_ = lean_box(0);
v_loc_x3f_4045_ = v___x_4114_;
v___y_4046_ = v_a_3929_;
v___y_4047_ = v_a_3930_;
v___y_4048_ = v_a_3931_;
v___y_4049_ = v_a_3932_;
v___y_4050_ = v_a_3933_;
v___y_4051_ = v_a_3934_;
v___y_4052_ = v_a_3935_;
v___y_4053_ = v_a_3936_;
goto v___jp_4044_;
}
v___jp_3982_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_inc_ref_n(v___y_3991_, 2);
v___x_4001_ = l_Array_append___redArg(v___y_3991_, v___y_4000_);
lean_dec_ref(v___y_4000_);
lean_inc_n(v___y_3984_, 2);
lean_inc_n(v___y_3994_, 3);
v___x_4002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4002_, 0, v___y_3994_);
lean_ctor_set(v___x_4002_, 1, v___y_3984_);
lean_ctor_set(v___x_4002_, 2, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4003_, 0, v___y_3994_);
lean_ctor_set(v___x_4003_, 1, v___y_3984_);
lean_ctor_set(v___x_4003_, 2, v___y_3991_);
v___x_4004_ = l_Lean_SourceInfo_fromRef(v___y_3999_, v___x_3979_);
lean_dec(v___y_3999_);
v___x_4005_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__3));
v___x_4006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
v___x_4007_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__4));
v___x_4009_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__5));
v___x_4010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___y_3994_);
lean_ctor_set(v___x_4010_, 1, v___x_4008_);
if (lean_obj_tag(v___y_3990_) == 0)
{
lean_object* v___x_4011_; 
v___x_4011_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_3941_ = v___y_3983_;
v___y_3942_ = v___y_3984_;
v___y_3943_ = v___y_3985_;
v___y_3944_ = v___y_3986_;
v___y_3945_ = v___y_3987_;
v___y_3946_ = v___x_4006_;
v___y_3947_ = v___y_3988_;
v___y_3948_ = v___x_4009_;
v___y_3949_ = v___x_4007_;
v___y_3950_ = v___y_3989_;
v___y_3951_ = v___x_4003_;
v___y_3952_ = v___y_3992_;
v___y_3953_ = v___y_3993_;
v___y_3954_ = v___y_3991_;
v___y_3955_ = v___x_4002_;
v___y_3956_ = v___x_4010_;
v___y_3957_ = v___y_3994_;
v___y_3958_ = v___y_3995_;
v___y_3959_ = v___y_3997_;
v___y_3960_ = v___y_3996_;
v___y_3961_ = v___y_3998_;
v___y_3962_ = v___x_4011_;
goto v___jp_3940_;
}
else
{
lean_object* v_val_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_val_4012_ = lean_ctor_get(v___y_3990_, 0);
lean_inc(v_val_4012_);
lean_dec_ref(v___y_3990_);
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___x_4014_ = lean_array_push(v___x_4013_, v_val_4012_);
v___y_3941_ = v___y_3983_;
v___y_3942_ = v___y_3984_;
v___y_3943_ = v___y_3985_;
v___y_3944_ = v___y_3986_;
v___y_3945_ = v___y_3987_;
v___y_3946_ = v___x_4006_;
v___y_3947_ = v___y_3988_;
v___y_3948_ = v___x_4009_;
v___y_3949_ = v___x_4007_;
v___y_3950_ = v___y_3989_;
v___y_3951_ = v___x_4003_;
v___y_3952_ = v___y_3992_;
v___y_3953_ = v___y_3993_;
v___y_3954_ = v___y_3991_;
v___y_3955_ = v___x_4002_;
v___y_3956_ = v___x_4010_;
v___y_3957_ = v___y_3994_;
v___y_3958_ = v___y_3995_;
v___y_3959_ = v___y_3997_;
v___y_3960_ = v___y_3996_;
v___y_3961_ = v___y_3998_;
v___y_3962_ = v___x_4014_;
goto v___jp_3940_;
}
}
v___jp_4016_:
{
lean_object* v_ref_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_ref_4031_ = lean_ctor_get(v___y_4020_, 5);
v___x_4032_ = 0;
v___x_4033_ = l_Lean_SourceInfo_fromRef(v_ref_4031_, v___x_4032_);
v___x_4034_ = l_Lean_SourceInfo_fromRef(v_tk_4015_, v___x_3979_);
lean_dec(v_tk_4015_);
v___x_4035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v___x_3938_);
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4037_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalConv___closed__7, &l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once, _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7);
if (lean_obj_tag(v___y_4018_) == 1)
{
lean_object* v_val_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_val_4038_ = lean_ctor_get(v___y_4018_, 0);
lean_inc(v_val_4038_);
lean_dec_ref(v___y_4018_);
v___x_4039_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__8));
lean_inc(v___x_4033_);
v___x_4040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4033_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Array_mkArray2___redArg(v___x_4040_, v_val_4038_);
v___y_3983_ = v___y_4017_;
v___y_3984_ = v___x_4036_;
v___y_3985_ = v___x_4035_;
v___y_3986_ = v___y_4019_;
v___y_3987_ = v___y_4020_;
v___y_3988_ = v___y_4021_;
v___y_3989_ = v___y_4022_;
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___x_4037_;
v___y_3992_ = v___y_4023_;
v___y_3993_ = v___y_4024_;
v___y_3994_ = v___x_4033_;
v___y_3995_ = v___y_4025_;
v___y_3996_ = v___y_4026_;
v___y_3997_ = v___y_4027_;
v___y_3998_ = v___y_4028_;
v___y_3999_ = v___y_4029_;
v___y_4000_ = v___x_4041_;
goto v___jp_3982_;
}
else
{
lean_object* v___x_4042_; 
lean_dec(v___y_4018_);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_3983_ = v___y_4017_;
v___y_3984_ = v___x_4036_;
v___y_3985_ = v___x_4035_;
v___y_3986_ = v___y_4019_;
v___y_3987_ = v___y_4020_;
v___y_3988_ = v___y_4021_;
v___y_3989_ = v___y_4022_;
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___x_4037_;
v___y_3992_ = v___y_4023_;
v___y_3993_ = v___y_4024_;
v___y_3994_ = v___x_4033_;
v___y_3995_ = v___y_4025_;
v___y_3996_ = v___y_4026_;
v___y_3997_ = v___y_4027_;
v___y_3998_ = v___y_4028_;
v___y_3999_ = v___y_4029_;
v___y_4000_ = v___x_4042_;
goto v___jp_3982_;
}
}
v___jp_4044_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4054_ = lean_unsigned_to_nat(2u);
v___x_4055_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4054_);
v___x_4056_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4055_);
v___x_4057_ = l_Lean_Syntax_matchesNull(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
uint8_t v___x_4058_; 
v___x_4058_ = l_Lean_Syntax_matchesNull(v___x_4055_, v___x_3981_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; 
lean_dec(v_loc_x3f_4045_);
lean_dec(v_tk_4015_);
lean_dec(v_stx_3928_);
v___x_4059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4059_;
}
else
{
lean_object* v_fileName_4060_; lean_object* v_fileMap_4061_; lean_object* v_options_4062_; lean_object* v_currRecDepth_4063_; lean_object* v_maxRecDepth_4064_; lean_object* v_ref_4065_; lean_object* v_currNamespace_4066_; lean_object* v_openDecls_4067_; lean_object* v_initHeartbeats_4068_; lean_object* v_maxHeartbeats_4069_; lean_object* v_quotContext_4070_; lean_object* v_currMacroScope_4071_; uint8_t v_diag_4072_; lean_object* v_cancelTk_x3f_4073_; uint8_t v_suppressElabErrors_4074_; lean_object* v_inheritedTraceOptions_4075_; lean_object* v_arr_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v_ref_4085_; lean_object* v___x_4086_; 
v_fileName_4060_ = lean_ctor_get(v___y_4052_, 0);
v_fileMap_4061_ = lean_ctor_get(v___y_4052_, 1);
v_options_4062_ = lean_ctor_get(v___y_4052_, 2);
v_currRecDepth_4063_ = lean_ctor_get(v___y_4052_, 3);
v_maxRecDepth_4064_ = lean_ctor_get(v___y_4052_, 4);
v_ref_4065_ = lean_ctor_get(v___y_4052_, 5);
v_currNamespace_4066_ = lean_ctor_get(v___y_4052_, 6);
v_openDecls_4067_ = lean_ctor_get(v___y_4052_, 7);
v_initHeartbeats_4068_ = lean_ctor_get(v___y_4052_, 8);
v_maxHeartbeats_4069_ = lean_ctor_get(v___y_4052_, 9);
v_quotContext_4070_ = lean_ctor_get(v___y_4052_, 10);
v_currMacroScope_4071_ = lean_ctor_get(v___y_4052_, 11);
v_diag_4072_ = lean_ctor_get_uint8(v___y_4052_, sizeof(void*)*14);
v_cancelTk_x3f_4073_ = lean_ctor_get(v___y_4052_, 12);
v_suppressElabErrors_4074_ = lean_ctor_get_uint8(v___y_4052_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4075_ = lean_ctor_get(v___y_4052_, 13);
v_arr_4076_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4056_);
v___x_4077_ = lean_unsigned_to_nat(4u);
v___x_4078_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4077_);
lean_dec(v_stx_3928_);
v___x_4079_ = lean_mk_empty_array_with_capacity(v___x_4054_);
v___x_4080_ = lean_array_push(v___x_4079_, v_tk_4015_);
v___x_4081_ = lean_array_push(v___x_4080_, v_arr_4076_);
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4083_ = lean_box(2);
v___x_4084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
lean_ctor_set(v___x_4084_, 1, v___x_4082_);
lean_ctor_set(v___x_4084_, 2, v___x_4081_);
v_ref_4085_ = l_Lean_replaceRef(v___x_4084_, v_ref_4065_);
lean_dec_ref(v___x_4084_);
lean_inc_ref(v_inheritedTraceOptions_4075_);
lean_inc(v_cancelTk_x3f_4073_);
lean_inc(v_currMacroScope_4071_);
lean_inc(v_quotContext_4070_);
lean_inc(v_maxHeartbeats_4069_);
lean_inc(v_initHeartbeats_4068_);
lean_inc(v_openDecls_4067_);
lean_inc(v_currNamespace_4066_);
lean_inc(v_maxRecDepth_4064_);
lean_inc(v_currRecDepth_4063_);
lean_inc_ref(v_options_4062_);
lean_inc_ref(v_fileMap_4061_);
lean_inc_ref(v_fileName_4060_);
v___x_4086_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4086_, 0, v_fileName_4060_);
lean_ctor_set(v___x_4086_, 1, v_fileMap_4061_);
lean_ctor_set(v___x_4086_, 2, v_options_4062_);
lean_ctor_set(v___x_4086_, 3, v_currRecDepth_4063_);
lean_ctor_set(v___x_4086_, 4, v_maxRecDepth_4064_);
lean_ctor_set(v___x_4086_, 5, v_ref_4085_);
lean_ctor_set(v___x_4086_, 6, v_currNamespace_4066_);
lean_ctor_set(v___x_4086_, 7, v_openDecls_4067_);
lean_ctor_set(v___x_4086_, 8, v_initHeartbeats_4068_);
lean_ctor_set(v___x_4086_, 9, v_maxHeartbeats_4069_);
lean_ctor_set(v___x_4086_, 10, v_quotContext_4070_);
lean_ctor_set(v___x_4086_, 11, v_currMacroScope_4071_);
lean_ctor_set(v___x_4086_, 12, v_cancelTk_x3f_4073_);
lean_ctor_set(v___x_4086_, 13, v_inheritedTraceOptions_4075_);
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*14, v_diag_4072_);
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*14 + 1, v_suppressElabErrors_4074_);
if (lean_obj_tag(v_loc_x3f_4045_) == 1)
{
lean_object* v_val_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_val_4087_ = lean_ctor_get(v_loc_x3f_4045_, 0);
lean_inc(v_val_4087_);
lean_dec_ref(v_loc_x3f_4045_);
v___x_4088_ = l_Lean_TSyntax_getId(v_val_4087_);
lean_dec(v_val_4087_);
v___x_4089_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v___x_4078_, v___x_4088_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___x_4086_, v___y_4053_);
lean_dec_ref(v___x_4086_);
return v___x_4089_;
}
else
{
lean_object* v___x_4090_; 
lean_dec(v_loc_x3f_4045_);
v___x_4090_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v___x_4078_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___x_4086_, v___y_4053_);
lean_dec_ref(v___x_4086_);
return v___x_4090_;
}
}
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v_arr_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4091_ = l_Lean_Syntax_getArg(v___x_4055_, v___x_4043_);
v___x_4092_ = l_Lean_Syntax_getArg(v___x_4055_, v___x_4054_);
lean_dec(v___x_4055_);
v_arr_4093_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4056_);
v___x_4094_ = lean_unsigned_to_nat(4u);
v___x_4095_ = l_Lean_Syntax_getArg(v_stx_3928_, v___x_4094_);
lean_dec(v_stx_3928_);
v___x_4096_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_4097_ = l_Lean_Syntax_getOptional_x3f(v___x_4091_);
lean_dec(v___x_4091_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_box(0);
v___y_4017_ = v___x_4092_;
v___y_4018_ = v_loc_x3f_4045_;
v___y_4019_ = v___y_4050_;
v___y_4020_ = v___y_4052_;
v___y_4021_ = v___y_4049_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4053_;
v___y_4024_ = v___y_4046_;
v___y_4025_ = v___x_4096_;
v___y_4026_ = v___x_4095_;
v___y_4027_ = v___y_4051_;
v___y_4028_ = v___y_4048_;
v___y_4029_ = v_arr_4093_;
v___y_4030_ = v___x_4098_;
goto v___jp_4016_;
}
else
{
lean_object* v_val_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_val_4099_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4097_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_val_4099_);
lean_dec(v___x_4097_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_val_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
v___y_4017_ = v___x_4092_;
v___y_4018_ = v_loc_x3f_4045_;
v___y_4019_ = v___y_4050_;
v___y_4020_ = v___y_4052_;
v___y_4021_ = v___y_4049_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4053_;
v___y_4024_ = v___y_4046_;
v___y_4025_ = v___x_4096_;
v___y_4026_ = v___x_4095_;
v___y_4027_ = v___y_4051_;
v___y_4028_ = v___y_4048_;
v___y_4029_ = v_arr_4093_;
v___y_4030_ = v___x_4104_;
goto v___jp_4016_;
}
}
}
}
}
}
v___jp_3940_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_inc_ref(v___y_3954_);
v___x_3963_ = l_Array_append___redArg(v___y_3954_, v___y_3962_);
lean_dec_ref(v___y_3962_);
lean_inc_n(v___y_3942_, 2);
lean_inc_n(v___y_3957_, 9);
v___x_3964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3964_, 0, v___y_3957_);
lean_ctor_set(v___x_3964_, 1, v___y_3942_);
lean_ctor_set(v___x_3964_, 2, v___x_3963_);
lean_inc(v___y_3948_);
v___x_3965_ = l_Lean_Syntax_node3(v___y_3957_, v___y_3948_, v___y_3956_, v___x_3964_, v___y_3941_);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__2));
v___x_3967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___y_3957_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_3970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___y_3957_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_3972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___y_3957_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = l_Lean_Syntax_node3(v___y_3957_, v___x_3968_, v___x_3970_, v___y_3960_, v___x_3972_);
v___x_3974_ = l_Lean_Syntax_node3(v___y_3957_, v___y_3942_, v___x_3965_, v___x_3967_, v___x_3973_);
lean_inc(v___y_3949_);
v___x_3975_ = l_Lean_Syntax_node1(v___y_3957_, v___y_3949_, v___x_3974_);
lean_inc(v___y_3958_);
v___x_3976_ = l_Lean_Syntax_node1(v___y_3957_, v___y_3958_, v___x_3975_);
v___x_3977_ = l_Lean_Syntax_node5(v___y_3957_, v___x_3939_, v___y_3943_, v___y_3955_, v___y_3951_, v___y_3946_, v___x_3976_);
v___x_3978_ = l_Lean_Elab_Tactic_evalTactic(v___x_3977_, v___y_3953_, v___y_3950_, v___y_3961_, v___y_3947_, v___y_3944_, v___y_3959_, v___y_3945_, v___y_3952_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object* v_stx_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Elab_Tactic_Conv_evalConv(v_stx_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4134_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4135_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
v___x_4136_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConv___boxed), 10, 0);
v___x_4138_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4134_, v___x_4135_, v___x_4136_, v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3(){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4168_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6));
v___x_4169_ = l_Lean_addBuiltinDeclarationRanges(v___x_4167_, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_Elab_Tactic_evalFirst(v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Elab_Tactic_Conv_evalFirst(v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(){
_start:
{
lean_object* v___f_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___f_4210_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0));
v___x_4211_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2));
v___x_4213_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4214_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4211_, v___x_4212_, v___x_4213_, v___f_4210_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3(){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4244_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6));
v___x_4245_ = l_Lean_addBuiltinDeclarationRanges(v___x_4243_, v___x_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
return v_res_4247_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
