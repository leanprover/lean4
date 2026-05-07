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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
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
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "whnf"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 111, 86, 148, 119, 255, 116, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalWhnf"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(6, 30, 125, 115, 1, 6, 125, 181)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(91) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 127, 28, 249, 1, 118, 43, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalReduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 147, 193, 102, 100, 242, 130, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 143, 59, 185, 170, 152, 3, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalZeta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 15, 219, 249, 19, 201, 139, 5)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 78, 175, 7, 2, 107, 214, 173)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalClear"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 199, 47, 127, 237, 69, 197, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 35, 202, 76, 198, 168, 114, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 70, 8, 168, 147, 123, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(110) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeqBracketed"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 46, 60, 206, 104, 220, 125, 67)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeqBracketed"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(96, 134, 88, 86, 62, 164, 138, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nestedConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 174, 232, 149, 164, 188, 109, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalNestedConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 69, 109, 55, 136, 241, 183, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 81, 30, 13, 252, 23, 29, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 126, 12, 172, 125, 122, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(124) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 85, 97, 250, 95, 212, 248, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalConvConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 138, 122, 156, 99, 134, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(129) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(4, 172, 52, 155, 88, 222, 189, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalParen"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 44, 38, 199, 32, 20, 2, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(132) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 23, 62, 30, 134, 160, 158, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalNestedTacticCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 57, 78, 97, 88, 231, 178, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(149) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNestedTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 223, 79, 147, 100, 241, 140, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 239, 251, 250, 179, 30, 250, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalConvTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 197, 60, 184, 130, 138, 183, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(160) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 39, 103, 162, 58, 5, 181, 114)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 46, 136, 31, 44, 193, 131, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(185) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalFirst___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 113, 181, 219, 229, 158, 34, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalFirst"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 17, 248, 44, 249, 130, 220, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(188) << 1) | 1)),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object*);
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
v_tail_234_ = lean_ctor_get(v_as_x27_225_, 1);
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
lean_inc(v_head_233_);
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
v___y_239_ = v___x_252_;
goto v___jp_238_;
}
}
else
{
lean_dec(v_a_236_);
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
lean_dec(v_as_x27_277_);
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
lean_dec(v_a_406_);
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
lean_dec(v_as_x27_460_);
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
size_t v_x_1695__boxed_942_; size_t v_x_1696__boxed_943_; lean_object* v_res_944_; 
v_x_1695__boxed_942_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_x_1696__boxed_943_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_937_, v_x_1695__boxed_942_, v_x_1696__boxed_943_, v_x_940_, v_x_941_);
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
lean_object* v___x_956_; lean_object* v_mctx_957_; lean_object* v_cache_958_; lean_object* v_zetaDeltaFVarIds_959_; lean_object* v_postponed_960_; lean_object* v_diag_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_989_; 
v___x_956_ = lean_st_ref_take(v___y_954_);
v_mctx_957_ = lean_ctor_get(v___x_956_, 0);
v_cache_958_ = lean_ctor_get(v___x_956_, 1);
v_zetaDeltaFVarIds_959_ = lean_ctor_get(v___x_956_, 2);
v_postponed_960_ = lean_ctor_get(v___x_956_, 3);
v_diag_961_ = lean_ctor_get(v___x_956_, 4);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_989_ == 0)
{
v___x_963_ = v___x_956_;
v_isShared_964_ = v_isSharedCheck_989_;
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
v_isShared_964_ = v_isSharedCheck_989_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_depth_965_; lean_object* v_levelAssignDepth_966_; lean_object* v_lmvarCounter_967_; lean_object* v_mvarCounter_968_; lean_object* v_lDecls_969_; lean_object* v_decls_970_; lean_object* v_userNames_971_; lean_object* v_lAssignment_972_; lean_object* v_eAssignment_973_; lean_object* v_dAssignment_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_988_; 
v_depth_965_ = lean_ctor_get(v_mctx_957_, 0);
v_levelAssignDepth_966_ = lean_ctor_get(v_mctx_957_, 1);
v_lmvarCounter_967_ = lean_ctor_get(v_mctx_957_, 2);
v_mvarCounter_968_ = lean_ctor_get(v_mctx_957_, 3);
v_lDecls_969_ = lean_ctor_get(v_mctx_957_, 4);
v_decls_970_ = lean_ctor_get(v_mctx_957_, 5);
v_userNames_971_ = lean_ctor_get(v_mctx_957_, 6);
v_lAssignment_972_ = lean_ctor_get(v_mctx_957_, 7);
v_eAssignment_973_ = lean_ctor_get(v_mctx_957_, 8);
v_dAssignment_974_ = lean_ctor_get(v_mctx_957_, 9);
v_isSharedCheck_988_ = !lean_is_exclusive(v_mctx_957_);
if (v_isSharedCheck_988_ == 0)
{
v___x_976_ = v_mctx_957_;
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_dAssignment_974_);
lean_inc(v_eAssignment_973_);
lean_inc(v_lAssignment_972_);
lean_inc(v_userNames_971_);
lean_inc(v_decls_970_);
lean_inc(v_lDecls_969_);
lean_inc(v_mvarCounter_968_);
lean_inc(v_lmvarCounter_967_);
lean_inc(v_levelAssignDepth_966_);
lean_inc(v_depth_965_);
lean_dec(v_mctx_957_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_eAssignment_973_, v_mvarId_952_, v_val_953_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 8, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_depth_965_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_levelAssignDepth_966_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_lmvarCounter_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_mvarCounter_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_lDecls_969_);
lean_ctor_set(v_reuseFailAlloc_987_, 5, v_decls_970_);
lean_ctor_set(v_reuseFailAlloc_987_, 6, v_userNames_971_);
lean_ctor_set(v_reuseFailAlloc_987_, 7, v_lAssignment_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 8, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 9, v_dAssignment_974_);
v___x_980_ = v_reuseFailAlloc_987_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_980_);
v___x_982_ = v___x_963_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_cache_958_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_zetaDeltaFVarIds_959_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_postponed_960_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_diag_961_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_st_ref_set(v___y_954_, v___x_982_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object* v_mvarId_990_, lean_object* v_val_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_990_, v_val_991_, v___y_992_);
lean_dec(v___y_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object* v_lhs_x27_995_, lean_object* v_h_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_998_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_998_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = l_Lean_Meta_mkEq(v_lhs_x27_995_, v_a_1009_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
lean_inc(v_a_1007_);
v___x_1012_ = l_Lean_MVarId_getTag(v_a_1007_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_mkLHSGoalRaw(v_a_1011_);
v___x_1015_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1014_, v_a_1013_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc_n(v_a_1016_, 2);
lean_dec_ref(v___x_1015_);
v___x_1017_ = l_Lean_Meta_mkEqTrans(v_h_996_, v_a_1016_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_a_1007_, v_a_1018_, v_a_1002_);
lean_dec_ref(v___x_1019_);
v___x_1020_ = l_Lean_Expr_mvarId_x21(v_a_1016_);
lean_dec(v_a_1016_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1022_, v_a_998_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1023_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_1016_);
lean_dec(v_a_1007_);
v_a_1024_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1017_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1017_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_1007_);
lean_dec_ref(v_h_996_);
v_a_1032_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1015_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1015_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_1011_);
lean_dec(v_a_1007_);
lean_dec_ref(v_h_996_);
v_a_1040_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1012_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1012_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_a_1007_);
lean_dec_ref(v_h_996_);
v_a_1048_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1010_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1010_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1007_);
lean_dec_ref(v_h_996_);
lean_dec_ref(v_lhs_x27_995_);
v_a_1056_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1008_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1008_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_h_996_);
lean_dec_ref(v_lhs_x27_995_);
v_a_1064_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1006_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1006_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object* v_lhs_x27_1072_, lean_object* v_h_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_lhs_x27_1072_, v_h_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object* v_mvarId_1084_, lean_object* v_val_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_1084_, v_val_1085_, v___y_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object* v_mvarId_1096_, lean_object* v_val_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(v_mvarId_1096_, v_val_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_x_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, size_t v_x_1115_, size_t v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
size_t v_x_2089__boxed_1126_; size_t v_x_2090__boxed_1127_; lean_object* v_res_1128_; 
v_x_2089__boxed_1126_ = lean_unbox_usize(v_x_1122_);
lean_dec(v_x_1122_);
v_x_2090__boxed_1127_ = lean_unbox_usize(v_x_1123_);
lean_dec(v_x_1123_);
v_res_1128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(v_00_u03b2_1120_, v_x_1121_, v_x_2089__boxed_1126_, v_x_2090__boxed_1127_, v_x_1124_, v_x_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1129_, lean_object* v_n_1130_, lean_object* v_k_1131_, lean_object* v_v_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1130_, v_k_1131_, v_v_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1134_, size_t v_depth_1135_, lean_object* v_keys_1136_, lean_object* v_vals_1137_, lean_object* v_heq_1138_, lean_object* v_i_1139_, lean_object* v_entries_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1135_, v_keys_1136_, v_vals_1137_, v_i_1139_, v_entries_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_depth_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_heq_1146_, lean_object* v_i_1147_, lean_object* v_entries_1148_){
_start:
{
size_t v_depth_boxed_1149_; lean_object* v_res_1150_; 
v_depth_boxed_1149_ = lean_unbox_usize(v_depth_1143_);
lean_dec(v_depth_1143_);
v_res_1150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1142_, v_depth_boxed_1149_, v_keys_1144_, v_vals_1145_, v_heq_1146_, v_i_1147_, v_entries_1148_);
lean_dec_ref(v_vals_1145_);
lean_dec_ref(v_keys_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1152_, v_x_1153_, v_x_1154_, v_x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object* v_lhs_x27_1157_, lean_object* v_a_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = l_Lean_Meta_mkEq(v_lhs_x27_1157_, v_a_1158_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = l_Lean_mkLHSGoalRaw(v_a_1171_);
v___x_1173_ = l_Lean_MVarId_replaceTargetDefEq(v_a_1169_, v___x_1172_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_a_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1176_, v___y_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1177_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1173_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1173_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_a_1169_);
v_a_1186_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1170_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1170_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_lhs_x27_1157_);
v_a_1194_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1168_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1168_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object* v_lhs_x27_1202_, lean_object* v_a_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(v_lhs_x27_1202_, v_a_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object* v_lhs_x27_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_1216_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1226_, 0, v_lhs_x27_1214_);
lean_closure_set(v___f_1226_, 1, v_a_1225_);
v___x_1227_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1226_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1227_;
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_lhs_x27_1214_);
v_a_1228_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1224_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1224_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object* v_lhs_x27_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_lhs_x27_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1248_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
v___x_1258_ = lean_whnf(v_a_1257_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1259_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
v_a_1261_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1258_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
v_a_1269_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1256_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1256_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___f_1297_; lean_object* v___x_1298_; 
v___f_1297_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0));
v___x_1298_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1297_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object* v_x_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object* v_x_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Elab_Tactic_Conv_evalWhnf(v_x_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_x_1320_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1351_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5));
v___x_1353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1354_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___boxed), 10, 0);
v___x_1355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1351_, v___x_1352_, v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3(){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6));
v___x_1386_ = l_Lean_addBuiltinDeclarationRanges(v___x_1384_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1390_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Meta_reduce(v_a_1399_, v___x_1400_, v___x_1400_, v___x_1400_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1402_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1403_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1401_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1401_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1398_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1398_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___f_1440_; lean_object* v___x_1441_; 
v___f_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0));
v___x_1441_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1440_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object* v_x_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Elab_Tactic_Conv_evalReduce(v_x_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_x_1463_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1489_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1));
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1492_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___boxed), 10, 0);
v___x_1493_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1489_, v___x_1490_, v___x_1491_, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3(){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6));
v___x_1524_ = l_Lean_addBuiltinDeclarationRanges(v___x_1522_, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1528_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v___x_1538_ = 1;
v___x_1539_ = l_Lean_Meta_zetaReduce(v_a_1537_, v___x_1538_, v___x_1538_, v___x_1538_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1540_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1539_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1539_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1536_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1536_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0));
v___x_1579_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1578_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object* v_x_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object* v_x_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Elab_Tactic_Conv_evalZeta(v_x_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_x_1601_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1627_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1));
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1630_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___boxed), 10, 0);
v___x_1631_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1627_, v___x_1628_, v___x_1629_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3(){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6));
v___x_1662_ = l_Lean_addBuiltinDeclarationRanges(v___x_1660_, v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(lean_object* v_e_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = l_Lean_Expr_hasMVar(v_e_1665_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_e_1665_);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v_mctx_1671_; lean_object* v___x_1672_; lean_object* v_fst_1673_; lean_object* v_snd_1674_; lean_object* v___x_1675_; lean_object* v_cache_1676_; lean_object* v_zetaDeltaFVarIds_1677_; lean_object* v_postponed_1678_; lean_object* v_diag_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1688_; 
v___x_1670_ = lean_st_ref_get(v___y_1666_);
v_mctx_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc_ref(v_mctx_1671_);
lean_dec(v___x_1670_);
v___x_1672_ = l_Lean_instantiateMVarsCore(v_mctx_1671_, v_e_1665_);
v_fst_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_fst_1673_);
v_snd_1674_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_snd_1674_);
lean_dec_ref(v___x_1672_);
v___x_1675_ = lean_st_ref_take(v___y_1666_);
v_cache_1676_ = lean_ctor_get(v___x_1675_, 1);
v_zetaDeltaFVarIds_1677_ = lean_ctor_get(v___x_1675_, 2);
v_postponed_1678_ = lean_ctor_get(v___x_1675_, 3);
v_diag_1679_ = lean_ctor_get(v___x_1675_, 4);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1675_, 0);
lean_dec(v_unused_1689_);
v___x_1681_ = v___x_1675_;
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_diag_1679_);
lean_inc(v_postponed_1678_);
lean_inc(v_zetaDeltaFVarIds_1677_);
lean_inc(v_cache_1676_);
lean_dec(v___x_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_snd_1674_);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_snd_1674_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_cache_1676_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_zetaDeltaFVarIds_1677_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_postponed_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_diag_1679_);
v___x_1684_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_st_ref_set(v___y_1666_, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_fst_1673_);
return v___x_1686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(lean_object* v_e_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1690_, v___y_1691_);
lean_dec(v___y_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(lean_object* v_e_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1694_, v___y_1696_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(lean_object* v_e_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(v_e_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object* v_mvarId_1708_, lean_object* v_fvarId_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; 
lean_inc(v_mvarId_1708_);
v___x_1715_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1708_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v_fst_1717_; lean_object* v_snd_1718_; lean_object* v___x_1719_; lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
v_fst_1717_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_fst_1717_);
v_snd_1718_ = lean_ctor_get(v_a_1716_, 1);
lean_inc(v_snd_1718_);
lean_dec(v_a_1716_);
v___x_1719_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_snd_1718_, v_a_1711_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = l_Lean_Expr_isMVar(v_a_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_a_1720_);
lean_dec(v_fst_1717_);
v___x_1722_ = l_Lean_MVarId_clear(v_mvarId_1708_, v_fvarId_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = l_Lean_Expr_mvarId_x21(v_a_1720_);
lean_dec(v_a_1720_);
lean_inc(v___x_1723_);
v___x_1724_ = l_Lean_MVarId_getKind(v___x_1723_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
lean_inc(v_fvarId_1709_);
v___x_1726_ = l_Lean_MVarId_clear(v___x_1723_, v_fvarId_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_n(v_a_1727_, 2);
lean_dec_ref(v___x_1726_);
v___x_1728_ = lean_unbox(v_a_1725_);
lean_dec(v_a_1725_);
v___x_1729_ = l_Lean_MVarId_setKind___redArg(v_a_1727_, v___x_1728_, v_a_1711_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v___x_1729_);
v___x_1730_ = l_Lean_mkMVar(v_a_1727_);
v___x_1731_ = l_Lean_Meta_mkEq(v_fst_1717_, v___x_1730_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = l_Lean_mkLHSGoalRaw(v_a_1732_);
v___x_1734_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1708_, v___x_1733_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Lean_MVarId_clear(v_a_1735_, v_fvarId_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1736_;
}
else
{
lean_dec(v_fvarId_1709_);
return v___x_1734_;
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_fvarId_1709_);
lean_dec(v_mvarId_1708_);
v_a_1737_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1731_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1731_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1727_);
lean_dec(v_fst_1717_);
lean_dec(v_fvarId_1709_);
lean_dec(v_mvarId_1708_);
v_a_1745_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1729_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1729_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_dec(v_a_1725_);
lean_dec(v_fst_1717_);
lean_dec(v_fvarId_1709_);
lean_dec(v_mvarId_1708_);
return v___x_1726_;
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v___x_1723_);
lean_dec(v_fst_1717_);
lean_dec(v_fvarId_1709_);
lean_dec(v_mvarId_1708_);
v_a_1753_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1724_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1724_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_fvarId_1709_);
lean_dec(v_mvarId_1708_);
v_a_1761_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1715_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1715_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
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
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object* v_mvarId_1769_, lean_object* v_fvarId_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_Tactic_Conv_convClear(v_mvarId_1769_, v_fvarId_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg(){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object* v_00_u03b1_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object* v_00_u03b1_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(v_00_u03b1_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object* v_a_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_sortFVarIds___redArg(v_a_1807_, v___y_1812_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object* v_a_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Elab_Tactic_Conv_evalClear___lam__0(v_a_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object* v_a_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1831_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Lean_Elab_Tactic_Conv_convClear(v_a_1840_, v_a_1829_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_a_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1844_, v___y_1831_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1841_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1841_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1829_);
v_a_1854_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1839_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1839_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object* v_a_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(v_a_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object* v_as_1873_, size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_b_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_b_1876_);
return v___x_1887_;
}
else
{
lean_object* v_a_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; 
v_a_1888_ = lean_array_uget_borrowed(v_as_1873_, v_i_1875_);
lean_inc(v_a_1888_);
v___f_1889_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1889_, 0, v_a_1888_);
v___x_1890_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1889_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; size_t v___x_1892_; size_t v___x_1893_; 
lean_dec_ref(v___x_1890_);
v___x_1891_ = lean_box(0);
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1875_, v___x_1892_);
v_i_1875_ = v___x_1893_;
v_b_1876_ = v___x_1891_;
goto _start;
}
else
{
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object* v_as_1895_, lean_object* v_sz_1896_, lean_object* v_i_1897_, lean_object* v_b_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1896_);
lean_dec(v_sz_1896_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1897_);
lean_dec(v_i_1897_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v_as_1895_, v_sz_boxed_1908_, v_i_boxed_1909_, v_b_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v_as_1895_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object* v_stx_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
lean_inc(v_stx_1918_);
v___x_1929_ = l_Lean_Syntax_isOfKind(v_stx_1918_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec(v_stx_1918_);
v___x_1930_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1930_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_hs_1933_; lean_object* v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = l_Lean_Syntax_getArg(v_stx_1918_, v___x_1931_);
lean_dec(v_stx_1918_);
v_hs_1933_ = l_Lean_Syntax_getArgs(v___x_1932_);
lean_dec(v___x_1932_);
v___x_1934_ = l_Lean_Elab_Tactic_getFVarIds(v_hs_1933_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
v___f_1936_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1936_, 0, v_a_1935_);
v___x_1937_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1936_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v___x_1939_ = l_Array_reverse___redArg(v_a_1938_);
v___x_1940_ = lean_box(0);
v_sz_1941_ = lean_array_size(v___x_1939_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v___x_1939_, v_sz_1941_, v___x_1942_, v___x_1940_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref(v___x_1939_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1940_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1940_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
return v___x_1943_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1937_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1937_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1934_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1934_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object* v_stx_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Elab_Tactic_Conv_evalClear(v_stx_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1(){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1));
v___x_1990_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___boxed), 10, 0);
v___x_1991_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1987_, v___x_1988_, v___x_1989_, v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_a_2008_; uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_1997_);
return v___x_2013_;
}
else
{
lean_object* v_next_2014_; 
v_next_2014_ = lean_ctor_get(v_b_1997_, 0);
lean_inc(v_next_2014_);
if (lean_obj_tag(v_next_2014_) == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_1997_);
return v___x_2015_;
}
else
{
lean_object* v_upperBound_2016_; lean_object* v_val_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2060_; 
v_upperBound_2016_ = lean_ctor_get(v_b_1997_, 1);
v_val_2017_ = lean_ctor_get(v_next_2014_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_next_2014_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2019_ = v_next_2014_;
v_isShared_2020_ = v_isSharedCheck_2060_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_val_2017_);
lean_dec(v_next_2014_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2060_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_nat_dec_lt(v_val_2017_, v_upperBound_2016_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_del_object(v___x_2019_);
lean_dec(v_val_2017_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_b_1997_);
return v___x_2022_;
}
else
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2057_; 
lean_inc(v_upperBound_2016_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_1997_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2058_ = lean_ctor_get(v_b_1997_, 1);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_b_1997_, 0);
lean_dec(v_unused_2059_);
v___x_2024_ = v_b_1997_;
v_isShared_2025_ = v_isSharedCheck_2057_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v_b_1997_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2057_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_1994_, v_i_1996_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_add(v_val_2017_, v___x_2027_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2028_);
v___x_2030_ = v___x_2019_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2030_);
v___x_2032_ = v___x_2024_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_upperBound_2016_);
v___x_2032_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2033_ = lean_unsigned_to_nat(2u);
v___x_2034_ = lean_nat_mod(v_val_2017_, v___x_2033_);
lean_dec(v_val_2017_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_nat_dec_eq(v___x_2034_, v___x_2035_);
lean_dec(v___x_2034_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; 
lean_inc(v_a_2026_);
v___x_2037_ = l_Lean_Elab_Tactic_saveTacticInfoForToken(v_a_2026_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_dec_ref(v___x_2037_);
v_a_2008_ = v___x_2032_;
goto v___jp_2007_;
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v___x_2032_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v___x_2046_; 
lean_inc(v_a_2026_);
v___x_2046_ = l_Lean_Elab_Tactic_evalTactic(v_a_2026_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_dec_ref(v___x_2046_);
v_a_2008_ = v___x_2032_;
goto v___jp_2007_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v___x_2032_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
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
v___jp_2007_:
{
size_t v___x_2009_; size_t v___x_2010_; 
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_1996_, v___x_2009_);
v_i_1996_ = v___x_2010_;
v_b_1997_ = v_a_2008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object* v_as_2061_, lean_object* v_sz_2062_, lean_object* v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2062_);
lean_dec(v_sz_2062_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v_as_2061_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_as_2061_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object* v_stx_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v___x_2089_ = l_Lean_Syntax_getArgs(v_stx_2079_);
v___x_2090_ = lean_array_get_size(v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0));
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
v_sz_2093_ = lean_array_size(v___x_2089_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v___x_2089_, v_sz_2093_, v___x_2094_, v___x_2092_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec_ref(v___x_2089_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2095_, 0);
lean_dec(v_unused_2104_);
v___x_2097_ = v___x_2095_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v___x_2095_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2095_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2095_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object* v_stx_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v_stx_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_stx_2113_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object* v_stx_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_unsigned_to_nat(0u);
v___x_2135_ = l_Lean_Syntax_getArg(v_stx_2124_, v___x_2134_);
v___x_2136_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2135_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object* v_stx_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(v_stx_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_stx_2137_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2163_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_2165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2166_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed), 10, 0);
v___x_2167_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2163_, v___x_2164_, v___x_2165_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3(){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6));
v___x_2198_ = l_Lean_addBuiltinDeclarationRanges(v___x_2196_, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object* v_a_2201_, lean_object* v_trees_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2207_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
v___x_2212_ = lean_apply_9(v_a_2201_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, lean_box(0));
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2221_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2213_);
lean_ctor_set(v___x_2217_, 1, v_trees_2202_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v_trees_2202_);
v_a_2222_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2212_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2212_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object* v_a_2230_, lean_object* v_trees_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(v_a_2230_, v_trees_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object* v___x_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2242_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object* v___x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(v___x_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object* v___y_2264_, lean_object* v_mkInfoTree_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v_a_2273_, lean_object* v_a_x3f_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_infoState_2277_; lean_object* v_trees_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_st_ref_get(v___y_2264_);
v_infoState_2277_ = lean_ctor_get(v___x_2276_, 7);
lean_inc_ref(v_infoState_2277_);
lean_dec(v___x_2276_);
v_trees_2278_ = lean_ctor_get(v_infoState_2277_, 2);
lean_inc_ref(v_trees_2278_);
lean_dec_ref(v_infoState_2277_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
v___x_2279_ = lean_apply_10(v_mkInfoTree_2265_, v_trees_2278_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2264_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2318_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2318_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2318_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v_infoState_2285_; lean_object* v_env_2286_; lean_object* v_nextMacroScope_2287_; lean_object* v_ngen_2288_; lean_object* v_auxDeclNGen_2289_; lean_object* v_traceState_2290_; lean_object* v_cache_2291_; lean_object* v_messages_2292_; lean_object* v_snapshotTasks_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2317_; 
v___x_2284_ = lean_st_ref_take(v___y_2264_);
v_infoState_2285_ = lean_ctor_get(v___x_2284_, 7);
v_env_2286_ = lean_ctor_get(v___x_2284_, 0);
v_nextMacroScope_2287_ = lean_ctor_get(v___x_2284_, 1);
v_ngen_2288_ = lean_ctor_get(v___x_2284_, 2);
v_auxDeclNGen_2289_ = lean_ctor_get(v___x_2284_, 3);
v_traceState_2290_ = lean_ctor_get(v___x_2284_, 4);
v_cache_2291_ = lean_ctor_get(v___x_2284_, 5);
v_messages_2292_ = lean_ctor_get(v___x_2284_, 6);
v_snapshotTasks_2293_ = lean_ctor_get(v___x_2284_, 8);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2295_ = v___x_2284_;
v_isShared_2296_ = v_isSharedCheck_2317_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snapshotTasks_2293_);
lean_inc(v_infoState_2285_);
lean_inc(v_messages_2292_);
lean_inc(v_cache_2291_);
lean_inc(v_traceState_2290_);
lean_inc(v_auxDeclNGen_2289_);
lean_inc(v_ngen_2288_);
lean_inc(v_nextMacroScope_2287_);
lean_inc(v_env_2286_);
lean_dec(v___x_2284_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2317_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint8_t v_enabled_2297_; lean_object* v_assignment_2298_; lean_object* v_lazyAssignment_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2315_; 
v_enabled_2297_ = lean_ctor_get_uint8(v_infoState_2285_, sizeof(void*)*3);
v_assignment_2298_ = lean_ctor_get(v_infoState_2285_, 0);
v_lazyAssignment_2299_ = lean_ctor_get(v_infoState_2285_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_infoState_2285_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v_infoState_2285_, 2);
lean_dec(v_unused_2316_);
v___x_2301_ = v_infoState_2285_;
v_isShared_2302_ = v_isSharedCheck_2315_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_lazyAssignment_2299_);
lean_inc(v_assignment_2298_);
lean_dec(v_infoState_2285_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2315_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = l_Lean_PersistentArray_push___redArg(v_a_2273_, v_a_2280_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 2, v___x_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_assignment_2298_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_lazyAssignment_2299_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v___x_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*3, v_enabled_2297_);
v___x_2305_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 7, v___x_2305_);
v___x_2307_ = v___x_2295_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_env_2286_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_nextMacroScope_2287_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_ngen_2288_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_auxDeclNGen_2289_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_traceState_2290_);
lean_ctor_set(v_reuseFailAlloc_2313_, 5, v_cache_2291_);
lean_ctor_set(v_reuseFailAlloc_2313_, 6, v_messages_2292_);
lean_ctor_set(v_reuseFailAlloc_2313_, 7, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2313_, 8, v_snapshotTasks_2293_);
v___x_2307_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2308_ = lean_st_ref_set(v___y_2264_, v___x_2307_);
v___x_2309_ = lean_box(0);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2309_);
v___x_2311_ = v___x_2282_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_a_2273_);
v_a_2319_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2279_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2279_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(lean_object* v___y_2327_, lean_object* v_mkInfoTree_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v_a_2336_, lean_object* v_a_x3f_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2327_, v_mkInfoTree_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v_a_2336_, v_a_x3f_2337_);
lean_dec(v_a_x3f_2337_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2327_);
return v_res_2339_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_unsigned_to_nat(32u);
v___x_2341_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2343_ = ((size_t)5ULL);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_unsigned_to_nat(32u);
v___x_2346_ = lean_mk_empty_array_with_capacity(v___x_2345_);
v___x_2347_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0);
v___x_2348_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2346_);
lean_ctor_set(v___x_2348_, 2, v___x_2344_);
lean_ctor_set(v___x_2348_, 3, v___x_2344_);
lean_ctor_set_usize(v___x_2348_, 4, v___x_2343_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v_infoState_2352_; lean_object* v_trees_2353_; lean_object* v___x_2354_; lean_object* v_infoState_2355_; lean_object* v_env_2356_; lean_object* v_nextMacroScope_2357_; lean_object* v_ngen_2358_; lean_object* v_auxDeclNGen_2359_; lean_object* v_traceState_2360_; lean_object* v_cache_2361_; lean_object* v_messages_2362_; lean_object* v_snapshotTasks_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2384_; 
v___x_2351_ = lean_st_ref_get(v___y_2349_);
v_infoState_2352_ = lean_ctor_get(v___x_2351_, 7);
lean_inc_ref(v_infoState_2352_);
lean_dec(v___x_2351_);
v_trees_2353_ = lean_ctor_get(v_infoState_2352_, 2);
lean_inc_ref(v_trees_2353_);
lean_dec_ref(v_infoState_2352_);
v___x_2354_ = lean_st_ref_take(v___y_2349_);
v_infoState_2355_ = lean_ctor_get(v___x_2354_, 7);
v_env_2356_ = lean_ctor_get(v___x_2354_, 0);
v_nextMacroScope_2357_ = lean_ctor_get(v___x_2354_, 1);
v_ngen_2358_ = lean_ctor_get(v___x_2354_, 2);
v_auxDeclNGen_2359_ = lean_ctor_get(v___x_2354_, 3);
v_traceState_2360_ = lean_ctor_get(v___x_2354_, 4);
v_cache_2361_ = lean_ctor_get(v___x_2354_, 5);
v_messages_2362_ = lean_ctor_get(v___x_2354_, 6);
v_snapshotTasks_2363_ = lean_ctor_get(v___x_2354_, 8);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2365_ = v___x_2354_;
v_isShared_2366_ = v_isSharedCheck_2384_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_snapshotTasks_2363_);
lean_inc(v_infoState_2355_);
lean_inc(v_messages_2362_);
lean_inc(v_cache_2361_);
lean_inc(v_traceState_2360_);
lean_inc(v_auxDeclNGen_2359_);
lean_inc(v_ngen_2358_);
lean_inc(v_nextMacroScope_2357_);
lean_inc(v_env_2356_);
lean_dec(v___x_2354_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2384_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
uint8_t v_enabled_2367_; lean_object* v_assignment_2368_; lean_object* v_lazyAssignment_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2382_; 
v_enabled_2367_ = lean_ctor_get_uint8(v_infoState_2355_, sizeof(void*)*3);
v_assignment_2368_ = lean_ctor_get(v_infoState_2355_, 0);
v_lazyAssignment_2369_ = lean_ctor_get(v_infoState_2355_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_infoState_2355_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v_infoState_2355_, 2);
lean_dec(v_unused_2383_);
v___x_2371_ = v_infoState_2355_;
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_lazyAssignment_2369_);
lean_inc(v_assignment_2368_);
lean_dec(v_infoState_2355_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 2, v___x_2373_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_assignment_2368_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_lazyAssignment_2369_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v___x_2373_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*3, v_enabled_2367_);
v___x_2375_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 7, v___x_2375_);
v___x_2377_ = v___x_2365_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_env_2356_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_nextMacroScope_2357_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_ngen_2358_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_auxDeclNGen_2359_);
lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_traceState_2360_);
lean_ctor_set(v_reuseFailAlloc_2380_, 5, v_cache_2361_);
lean_ctor_set(v_reuseFailAlloc_2380_, 6, v_messages_2362_);
lean_ctor_set(v_reuseFailAlloc_2380_, 7, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2380_, 8, v_snapshotTasks_2363_);
v___x_2377_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_st_ref_set(v___y_2349_, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_trees_2353_);
return v___x_2379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2385_);
lean_dec(v___y_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object* v_x_2388_, lean_object* v_mkInfoTree_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; lean_object* v_infoState_2400_; uint8_t v_enabled_2401_; 
v___x_2399_ = lean_st_ref_get(v___y_2397_);
v_infoState_2400_ = lean_ctor_get(v___x_2399_, 7);
lean_inc_ref(v_infoState_2400_);
lean_dec(v___x_2399_);
v_enabled_2401_ = lean_ctor_get_uint8(v_infoState_2400_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2400_);
if (v_enabled_2401_ == 0)
{
lean_object* v___x_2402_; 
lean_dec_ref(v_mkInfoTree_2389_);
lean_inc(v___y_2397_);
lean_inc_ref(v___y_2396_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
v___x_2402_ = lean_apply_9(v_x_2388_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, lean_box(0));
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; lean_object* v_a_2404_; lean_object* v_r_2405_; 
v___x_2403_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2397_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
lean_inc(v___y_2397_);
lean_inc_ref(v___y_2396_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
v_r_2405_ = lean_apply_9(v_x_2388_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, lean_box(0));
if (lean_obj_tag(v_r_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2430_; 
v_a_2406_ = lean_ctor_get(v_r_2405_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_r_2405_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2408_ = v_r_2405_;
v_isShared_2409_ = v_isSharedCheck_2430_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v_r_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2430_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
lean_inc(v_a_2406_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 1);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2397_, v_mkInfoTree_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v_a_2404_, v___x_2411_);
lean_dec_ref(v___x_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v___x_2412_, 0);
lean_dec(v_unused_2420_);
v___x_2414_ = v___x_2412_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_dec(v___x_2412_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v_a_2406_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2406_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2406_);
v_a_2421_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2412_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2412_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_a_2431_ = lean_ctor_get(v_r_2405_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v_r_2405_);
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2397_, v_mkInfoTree_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v_a_2404_, v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v___x_2433_, 0);
lean_dec(v_unused_2441_);
v___x_2435_ = v___x_2433_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v___x_2433_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 1);
lean_ctor_set(v___x_2435_, 0, v_a_2431_);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2431_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2431_);
v_a_2442_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2433_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2433_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object* v_x_2450_, lean_object* v_mkInfoTree_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2450_, v_mkInfoTree_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object* v___f_2513_, lean_object* v___f_2514_, lean_object* v_stx_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___f_2513_, v___f_2514_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec_ref(v___x_2525_);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = l_Lean_Syntax_getArg(v_stx_2515_, v___x_2526_);
v___x_2528_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2527_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___x_2527_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_ref_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec_ref(v___x_2528_);
v_ref_2529_ = lean_ctor_get(v___y_2522_, 5);
v___x_2530_ = 0;
v___x_2531_ = l_Lean_SourceInfo_fromRef(v_ref_2529_, v___x_2530_);
v___x_2532_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1));
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2));
lean_inc_n(v___x_2531_, 22);
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_2536_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10));
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2531_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2531_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_2545_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
v___x_2546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2531_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_2548_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2531_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2547_, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2537_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2536_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2535_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node2(v___x_2531_, v___x_2544_, v___x_2546_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2537_, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2536_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2535_, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node2(v___x_2531_, v___x_2541_, v___x_2543_, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2537_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2536_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2535_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2531_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node3(v___x_2531_, v___x_2538_, v___x_2540_, v___x_2561_, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2537_, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2536_, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node1(v___x_2531_, v___x_2535_, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node2(v___x_2531_, v___x_2532_, v___x_2534_, v___x_2567_);
v___x_2569_ = l_Lean_Elab_Tactic_evalTactic(v___x_2568_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2569_;
}
else
{
return v___x_2528_;
}
}
else
{
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object* v___f_2570_, lean_object* v___f_2571_, lean_object* v_stx_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(v___f_2570_, v___f_2571_, v_stx_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v_stx_2572_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object* v_stx_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = l_Lean_Syntax_getArg(v_stx_2585_, v___x_2595_);
v___x_2597_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2596_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_fileName_2599_; lean_object* v_fileMap_2600_; lean_object* v_options_2601_; lean_object* v_currRecDepth_2602_; lean_object* v_maxRecDepth_2603_; lean_object* v_ref_2604_; lean_object* v_currNamespace_2605_; lean_object* v_openDecls_2606_; lean_object* v_initHeartbeats_2607_; lean_object* v_maxHeartbeats_2608_; lean_object* v_quotContext_2609_; lean_object* v_currMacroScope_2610_; uint8_t v_diag_2611_; lean_object* v_cancelTk_x3f_2612_; uint8_t v_suppressElabErrors_2613_; lean_object* v_inheritedTraceOptions_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v_ref_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v_fileName_2599_ = lean_ctor_get(v_a_2592_, 0);
v_fileMap_2600_ = lean_ctor_get(v_a_2592_, 1);
v_options_2601_ = lean_ctor_get(v_a_2592_, 2);
v_currRecDepth_2602_ = lean_ctor_get(v_a_2592_, 3);
v_maxRecDepth_2603_ = lean_ctor_get(v_a_2592_, 4);
v_ref_2604_ = lean_ctor_get(v_a_2592_, 5);
v_currNamespace_2605_ = lean_ctor_get(v_a_2592_, 6);
v_openDecls_2606_ = lean_ctor_get(v_a_2592_, 7);
v_initHeartbeats_2607_ = lean_ctor_get(v_a_2592_, 8);
v_maxHeartbeats_2608_ = lean_ctor_get(v_a_2592_, 9);
v_quotContext_2609_ = lean_ctor_get(v_a_2592_, 10);
v_currMacroScope_2610_ = lean_ctor_get(v_a_2592_, 11);
v_diag_2611_ = lean_ctor_get_uint8(v_a_2592_, sizeof(void*)*14);
v_cancelTk_x3f_2612_ = lean_ctor_get(v_a_2592_, 12);
v_suppressElabErrors_2613_ = lean_ctor_get_uint8(v_a_2592_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2614_ = lean_ctor_get(v_a_2592_, 13);
v___f_2615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2615_, 0, v_a_2598_);
v___x_2616_ = lean_unsigned_to_nat(2u);
v___x_2617_ = l_Lean_Syntax_getArg(v_stx_2585_, v___x_2616_);
v___f_2618_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0));
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2619_, 0, v___f_2618_);
lean_closure_set(v___f_2619_, 1, v___f_2615_);
lean_closure_set(v___f_2619_, 2, v_stx_2585_);
v_ref_2620_ = l_Lean_replaceRef(v___x_2617_, v_ref_2604_);
lean_dec(v___x_2617_);
lean_inc_ref(v_inheritedTraceOptions_2614_);
lean_inc(v_cancelTk_x3f_2612_);
lean_inc(v_currMacroScope_2610_);
lean_inc(v_quotContext_2609_);
lean_inc(v_maxHeartbeats_2608_);
lean_inc(v_initHeartbeats_2607_);
lean_inc(v_openDecls_2606_);
lean_inc(v_currNamespace_2605_);
lean_inc(v_maxRecDepth_2603_);
lean_inc(v_currRecDepth_2602_);
lean_inc_ref(v_options_2601_);
lean_inc_ref(v_fileMap_2600_);
lean_inc_ref(v_fileName_2599_);
v___x_2621_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2621_, 0, v_fileName_2599_);
lean_ctor_set(v___x_2621_, 1, v_fileMap_2600_);
lean_ctor_set(v___x_2621_, 2, v_options_2601_);
lean_ctor_set(v___x_2621_, 3, v_currRecDepth_2602_);
lean_ctor_set(v___x_2621_, 4, v_maxRecDepth_2603_);
lean_ctor_set(v___x_2621_, 5, v_ref_2620_);
lean_ctor_set(v___x_2621_, 6, v_currNamespace_2605_);
lean_ctor_set(v___x_2621_, 7, v_openDecls_2606_);
lean_ctor_set(v___x_2621_, 8, v_initHeartbeats_2607_);
lean_ctor_set(v___x_2621_, 9, v_maxHeartbeats_2608_);
lean_ctor_set(v___x_2621_, 10, v_quotContext_2609_);
lean_ctor_set(v___x_2621_, 11, v_currMacroScope_2610_);
lean_ctor_set(v___x_2621_, 12, v_cancelTk_x3f_2612_);
lean_ctor_set(v___x_2621_, 13, v_inheritedTraceOptions_2614_);
lean_ctor_set_uint8(v___x_2621_, sizeof(void*)*14, v_diag_2611_);
lean_ctor_set_uint8(v___x_2621_, sizeof(void*)*14 + 1, v_suppressElabErrors_2613_);
v___x_2622_ = l_Lean_Elab_Tactic_closeUsingOrAdmit(v___f_2619_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v___x_2621_, v_a_2593_);
lean_dec_ref(v___x_2621_);
return v___x_2622_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_stx_2585_);
v_a_2623_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2597_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2597_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object* v_stx_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v_stx_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object* v_00_u03b1_2662_, lean_object* v_x_2663_, lean_object* v_mkInfoTree_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2663_, v_mkInfoTree_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_x_2676_, lean_object* v_mkInfoTree_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(v_00_u03b1_2675_, v_x_2676_, v_mkInfoTree_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2703_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1));
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2706_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed), 10, 0);
v___x_2707_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2703_, v___x_2704_, v___x_2705_, v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3(){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6));
v___x_2738_ = l_Lean_addBuiltinDeclarationRanges(v___x_2736_, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object* v_stx_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = l_Lean_Syntax_getArg(v_stx_2741_, v___x_2751_);
v___x_2753_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v___x_2752_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object* v_stx_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Elab_Tactic_Conv_evalNestedConv(v_stx_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_stx_2754_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2780_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1));
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed), 10, 0);
v___x_2784_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2780_, v___x_2781_, v___x_2782_, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3(){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6));
v___x_2815_ = l_Lean_addBuiltinDeclarationRanges(v___x_2813_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object* v_stx_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_unsigned_to_nat(0u);
v___x_2829_ = l_Lean_Syntax_getArg(v_stx_2818_, v___x_2828_);
v___x_2830_ = l_Lean_Elab_Tactic_evalTactic(v___x_2829_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object* v_stx_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_Tactic_Conv_evalConvSeq(v_stx_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_stx_2831_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2857_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_2859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed), 10, 0);
v___x_2861_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2857_, v___x_2858_, v___x_2859_, v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3(){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6));
v___x_2892_ = l_Lean_addBuiltinDeclarationRanges(v___x_2890_, v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object* v_stx_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_2897_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = lean_unsigned_to_nat(2u);
v___x_2908_ = l_Lean_Syntax_getArg(v_stx_2895_, v___x_2907_);
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = l_Lean_Syntax_getArg(v___x_2908_, v___x_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = l_Lean_Elab_Tactic_Conv_convert(v_a_2906_, v___x_2911_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v_fst_2914_; lean_object* v_snd_2915_; lean_object* v___x_2916_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v_fst_2914_ = lean_ctor_get(v_a_2913_, 0);
lean_inc(v_fst_2914_);
v_snd_2915_ = lean_ctor_get(v_a_2913_, 1);
lean_inc(v_snd_2915_);
lean_dec(v_a_2913_);
v___x_2916_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_fst_2914_, v_snd_2915_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_a_2917_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2912_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2912_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_a_2925_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2905_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2905_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object* v_stx_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(v_stx_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v_stx_2933_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object* v_stx_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___f_2954_; lean_object* v___x_2955_; 
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2954_, 0, v_stx_2944_);
v___x_2955_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2954_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object* v_stx_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq(v_stx_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2982_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1));
v___x_2984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_2985_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed), 10, 0);
v___x_2986_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2982_, v___x_2983_, v___x_2984_, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3(){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_3016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6));
v___x_3017_ = l_Lean_addBuiltinDeclarationRanges(v___x_3015_, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object* v_stx_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = l_Lean_Syntax_getArg(v_stx_3020_, v___x_3030_);
v___x_3032_ = l_Lean_Elab_Tactic_evalTactic(v___x_3031_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object* v_stx_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Elab_Tactic_Conv_evalParen(v_stx_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_stx_3033_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3058_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3061_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalParen___boxed), 10, 0);
v___x_3062_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3058_, v___x_3059_, v___x_3060_, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3(){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6));
v___x_3093_ = l_Lean_addBuiltinDeclarationRanges(v___x_3091_, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
lean_inc(v___y_3100_);
lean_inc_ref(v___y_3099_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
v___x_3106_ = lean_apply_9(v_x_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, lean_box(0));
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object* v_mvarId_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___f_3129_; lean_object* v___x_3130_; 
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
v___f_3129_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3129_, 0, v_x_3119_);
lean_closure_set(v___f_3129_, 1, v___y_3120_);
lean_closure_set(v___f_3129_, 2, v___y_3121_);
lean_closure_set(v___f_3129_, 3, v___y_3122_);
lean_closure_set(v___f_3129_, 4, v___y_3123_);
v___x_3130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3118_, v___f_3129_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3130_) == 0)
{
return v___x_3130_;
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_3139_, lean_object* v_x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3139_, v_x_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object* v_00_u03b1_3151_, lean_object* v_mvarId_3152_, lean_object* v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3152_, v_x_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_mvarId_3165_, lean_object* v_x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(v_00_u03b1_3164_, v_mvarId_3165_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object* v_head_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; 
lean_inc(v_head_3177_);
v___x_3187_ = l_Lean_MVarId_getType(v_head_3177_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_n(v_a_3188_, 2);
lean_dec_ref(v___x_3187_);
v___x_3189_ = l_Lean_Meta_matchEq_x3f(v_a_3188_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3216_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3216_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3216_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
if (lean_obj_tag(v_a_3190_) == 1)
{
lean_object* v_val_3194_; lean_object* v_snd_3195_; lean_object* v_snd_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v_val_3194_ = lean_ctor_get(v_a_3190_, 0);
lean_inc(v_val_3194_);
lean_dec_ref(v_a_3190_);
v_snd_3195_ = lean_ctor_get(v_val_3194_, 1);
lean_inc(v_snd_3195_);
lean_dec(v_val_3194_);
v_snd_3196_ = lean_ctor_get(v_snd_3195_, 1);
lean_inc(v_snd_3196_);
lean_dec(v_snd_3195_);
v___x_3197_ = l_Lean_Expr_getAppFn(v_snd_3196_);
lean_dec(v_snd_3196_);
v___x_3198_ = l_Lean_Expr_isMVar(v___x_3197_);
lean_dec_ref(v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3200_; 
lean_dec(v_a_3188_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_head_3177_);
v___x_3200_ = v___x_3192_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_head_3177_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
else
{
lean_object* v___x_3202_; 
lean_del_object(v___x_3192_);
v___x_3202_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_3188_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref(v___x_3202_);
v___x_3204_ = l_Lean_MVarId_replaceTargetDefEq(v_head_3177_, v_a_3203_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3204_;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v_head_3177_);
v_a_3205_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3202_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3202_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
else
{
lean_object* v___x_3214_; 
lean_dec(v_a_3190_);
lean_dec(v_a_3188_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_head_3177_);
v___x_3214_ = v___x_3192_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_head_3177_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3188_);
lean_dec(v_head_3177_);
v_a_3217_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3189_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3189_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v_head_3177_);
v_a_3225_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3187_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3187_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object* v_head_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(v_head_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object* v_x_3244_, lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = l_List_reverse___redArg(v_x_3245_);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
else
{
lean_object* v_head_3257_; lean_object* v_tail_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3277_; 
v_head_3257_ = lean_ctor_get(v_x_3244_, 0);
v_tail_3258_ = lean_ctor_get(v_x_3244_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_x_3244_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3260_ = v_x_3244_;
v_isShared_3261_ = v_isSharedCheck_3277_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_tail_3258_);
lean_inc(v_head_3257_);
lean_dec(v_x_3244_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3277_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___f_3262_; lean_object* v___x_3263_; 
lean_inc(v_head_3257_);
v___f_3262_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3262_, 0, v_head_3257_);
v___x_3263_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_head_3257_, v___f_3262_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v_x_3245_);
lean_ctor_set(v___x_3260_, 0, v_a_3264_);
v___x_3266_ = v___x_3260_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3264_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_x_3245_);
v___x_3266_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
v_x_3244_ = v_tail_3258_;
v_x_3245_ = v___x_3266_;
goto _start;
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_del_object(v___x_3260_);
lean_dec(v_tail_3258_);
lean_dec(v_x_3245_);
v_a_3269_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3263_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3263_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_x_3278_, v_x_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = lean_box(0);
v___x_3302_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_a_3300_, v___x_3301_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_3303_, v_a_3291_);
return v___x_3304_;
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3302_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3302_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
v_a_3313_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3299_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3299_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object* v_stx_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; lean_object* v_seq_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_unsigned_to_nat(2u);
v_seq_3342_ = l_Lean_Syntax_getArg(v_stx_3331_, v___x_3341_);
v___x_3343_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3342_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref(v___x_3343_);
v___x_3344_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
return v___x_3344_;
}
else
{
return v___x_3343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object* v_stx_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(v_stx_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_stx_3345_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3371_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1));
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3374_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed), 10, 0);
v___x_3375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3371_, v___x_3372_, v___x_3373_, v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3(){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6));
v___x_3406_ = l_Lean_addBuiltinDeclarationRanges(v___x_3404_, v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object* v_seq_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v___x_3419_);
v___x_3420_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3420_;
}
else
{
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object* v_seq_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(v_seq_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object* v_a_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3434_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref(v___x_3442_);
v___x_3444_ = l_Lean_Expr_mdataExpr_x21(v_a_3432_);
v___x_3445_ = l_Lean_MVarId_replaceTargetDefEq(v_a_3443_, v___x_3444_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_a_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3448_, v___y_3434_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3445_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3445_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
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
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
v_a_3458_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3442_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3442_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object* v_a_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(v_a_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v_a_3466_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object* v_stx_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Elab_Tactic_getMainTarget(v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v_seq_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3487_);
v___x_3489_ = lean_unsigned_to_nat(2u);
v_seq_3490_ = l_Lean_Syntax_getArg(v_stx_3477_, v___x_3489_);
v___f_3491_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3491_, 0, v_seq_3490_);
v___x_3492_ = l_Lean_isLHSGoal_x3f(v_a_3488_);
if (lean_obj_tag(v___x_3492_) == 1)
{
lean_object* v___f_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v___x_3492_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3493_, 0, v_a_3488_);
v___x_3494_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3493_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3495_; 
lean_dec_ref(v___x_3494_);
v___x_3495_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3491_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
return v___x_3495_;
}
else
{
lean_dec_ref(v___f_3491_);
return v___x_3494_;
}
}
else
{
lean_object* v___x_3496_; 
lean_dec(v___x_3492_);
lean_dec(v_a_3488_);
v___x_3496_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3491_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
return v___x_3496_;
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_a_3497_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3487_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3487_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object* v_stx_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic(v_stx_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_stx_3505_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3531_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1));
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3534_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed), 10, 0);
v___x_3535_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3531_, v___x_3532_, v___x_3533_, v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3(){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6));
v___x_3566_ = l_Lean_addBuiltinDeclarationRanges(v___x_3564_, v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object* v_stx_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = lean_unsigned_to_nat(2u);
v___x_3580_ = l_Lean_Syntax_getArg(v_stx_3569_, v___x_3579_);
v___x_3581_ = l_Lean_Elab_Tactic_evalTactic(v___x_3580_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object* v_stx_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Elab_Tactic_Conv_evalConvTactic(v_stx_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_stx_3582_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3608_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1));
v___x_3610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3611_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed), 10, 0);
v___x_3612_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3608_, v___x_3609_, v___x_3610_, v___x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3(){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6));
v___x_3643_ = l_Lean_addBuiltinDeclarationRanges(v___x_3641_, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object* v_ref_3646_, lean_object* v___x_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_3646_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref(v___x_3657_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3659_, 0, v_a_3658_);
v___x_3660_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___x_3647_, v___f_3659_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3660_;
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v___x_3647_);
v_a_3661_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3657_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3657_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object* v_ref_3669_, lean_object* v___x_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(v_ref_3669_, v___x_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object* v_fst_3681_, lean_object* v_snd_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3684_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v___x_3694_ = l_Lean_MVarId_replaceTargetEq(v_a_3693_, v_fst_3681_, v_snd_3682_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
v___x_3696_ = lean_box(0);
v___x_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3697_, 0, v_a_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3697_, v___y_3684_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3694_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3694_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v_snd_3682_);
lean_dec_ref(v_fst_3681_);
v_a_3707_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3692_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3692_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object* v_fst_3715_, lean_object* v_snd_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(v_fst_3715_, v_snd_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object* v_conv_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Elab_Tactic_getMainTarget(v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v_ref_3739_; lean_object* v___x_3740_; lean_object* v___f_3741_; lean_object* v___x_3742_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v_ref_3739_ = lean_ctor_get(v___y_3734_, 5);
v___x_3740_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3740_, 0, v_conv_3727_);
lean_inc(v_ref_3739_);
v___f_3741_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3741_, 0, v_ref_3739_);
lean_closure_set(v___f_3741_, 1, v___x_3740_);
v___x_3742_ = l_Lean_Elab_Tactic_Conv_convert(v_a_3738_, v___f_3741_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v_fst_3744_; lean_object* v_snd_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3777_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref(v___x_3742_);
v_fst_3744_ = lean_ctor_get(v_a_3743_, 0);
v_snd_3745_ = lean_ctor_get(v_a_3743_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3747_ = v_a_3743_;
v_isShared_3748_ = v_isSharedCheck_3777_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_snd_3745_);
lean_inc(v_fst_3744_);
lean_dec(v_a_3743_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3777_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___f_3749_; lean_object* v___x_3750_; 
v___f_3749_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3749_, 0, v_fst_3744_);
lean_closure_set(v___f_3749_, 1, v_snd_3745_);
v___x_3750_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3749_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3750_) == 0)
{
uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec_ref(v___x_3750_);
v___x_3751_ = 0;
v___x_3752_ = l_Lean_SourceInfo_fromRef(v_ref_3739_, v___x_3751_);
v___x_3753_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_3754_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
lean_inc(v___x_3752_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 2);
lean_ctor_set(v___x_3747_, 1, v___x_3754_);
lean_ctor_set(v___x_3747_, 0, v___x_3752_);
v___x_3756_ = v___x_3747_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3757_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_3759_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_3760_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_3761_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
lean_inc_n(v___x_3752_, 10);
v___x_3762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3752_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_3764_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_3765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3752_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3763_, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3759_, v___x_3766_);
v___x_3768_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3758_, v___x_3767_);
v___x_3769_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3757_, v___x_3768_);
v___x_3770_ = l_Lean_Syntax_node2(v___x_3752_, v___x_3760_, v___x_3762_, v___x_3769_);
v___x_3771_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3759_, v___x_3770_);
v___x_3772_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3758_, v___x_3771_);
v___x_3773_ = l_Lean_Syntax_node1(v___x_3752_, v___x_3757_, v___x_3772_);
v___x_3774_ = l_Lean_Syntax_node2(v___x_3752_, v___x_3753_, v___x_3756_, v___x_3773_);
v___x_3775_ = l_Lean_Elab_Tactic_evalTactic(v___x_3774_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec_ref(v___y_3734_);
return v___x_3775_;
}
}
else
{
lean_del_object(v___x_3747_);
lean_dec_ref(v___y_3734_);
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v___y_3734_);
v_a_3778_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3742_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3742_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v___y_3734_);
lean_dec(v_conv_3727_);
v_a_3786_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3737_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3737_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object* v_conv_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(v_conv_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object* v_conv_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v___f_3815_; lean_object* v___x_3816_; 
v___f_3815_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3815_, 0, v_conv_3805_);
v___x_3816_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3815_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object* v_conv_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v_conv_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object* v_snd_3828_, lean_object* v___x_3829_, lean_object* v_fst_3830_, lean_object* v_a_3831_, lean_object* v___x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Meta_mkEqMP(v_snd_3828_, v___x_3829_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3840_, 0, v_fst_3830_);
v___x_3841_ = lean_box(0);
v___x_3842_ = l_Lean_MVarId_replace(v_a_3831_, v___x_3832_, v_a_3839_, v___x_3840_, v___x_3841_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3842_;
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v___x_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_fst_3830_);
v_a_3843_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3838_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3838_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object* v_snd_3851_, lean_object* v___x_3852_, lean_object* v_fst_3853_, lean_object* v_a_3854_, lean_object* v___x_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(v_snd_3851_, v___x_3852_, v_fst_3853_, v_a_3854_, v___x_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object* v_a_3862_, lean_object* v_snd_3863_, lean_object* v_fst_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3866_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; lean_object* v___x_3879_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc_n(v_a_3875_, 2);
lean_dec_ref(v___x_3874_);
v___x_3876_ = l_Lean_LocalDecl_fvarId(v_a_3862_);
lean_inc(v___x_3876_);
v___x_3877_ = l_Lean_mkFVar(v___x_3876_);
v___f_3878_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3878_, 0, v_snd_3863_);
lean_closure_set(v___f_3878_, 1, v___x_3877_);
lean_closure_set(v___f_3878_, 2, v_fst_3864_);
lean_closure_set(v___f_3878_, 3, v_a_3875_);
lean_closure_set(v___f_3878_, 4, v___x_3876_);
v___x_3879_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_a_3875_, v___f_3878_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_mvarId_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref(v___x_3879_);
v_mvarId_3881_ = lean_ctor_get(v_a_3880_, 1);
lean_inc(v_mvarId_3881_);
lean_dec(v_a_3880_);
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_mvarId_3881_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3883_, v___y_3866_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3884_;
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3879_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3879_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref(v_fst_3864_);
lean_dec_ref(v_snd_3863_);
v_a_3893_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3874_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3874_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object* v_a_3901_, lean_object* v_snd_3902_, lean_object* v_fst_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(v_a_3901_, v_snd_3902_, v_fst_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v_a_3901_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(lean_object* v_hUserName_3914_, lean_object* v_conv_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_Meta_getLocalDeclFromUserName(v_hUserName_3914_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v_ref_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___f_3930_; lean_object* v___x_3931_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v_ref_3927_ = lean_ctor_get(v___y_3922_, 5);
v___x_3928_ = l_Lean_LocalDecl_type(v_a_3926_);
v___x_3929_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3929_, 0, v_conv_3915_);
lean_inc(v_ref_3927_);
v___f_3930_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3930_, 0, v_ref_3927_);
lean_closure_set(v___f_3930_, 1, v___x_3929_);
v___x_3931_ = l_Lean_Elab_Tactic_Conv_convert(v___x_3928_, v___f_3930_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_fst_3933_; lean_object* v_snd_3934_; lean_object* v___f_3935_; lean_object* v___x_3936_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v___x_3931_);
v_fst_3933_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_fst_3933_);
v_snd_3934_ = lean_ctor_get(v_a_3932_, 1);
lean_inc(v_snd_3934_);
lean_dec(v_a_3932_);
v___f_3935_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3935_, 0, v_a_3926_);
lean_closure_set(v___f_3935_, 1, v_snd_3934_);
lean_closure_set(v___f_3935_, 2, v_fst_3933_);
v___x_3936_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3935_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec_ref(v___y_3922_);
return v___x_3936_;
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_a_3926_);
lean_dec_ref(v___y_3922_);
v_a_3937_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3931_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3931_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___y_3922_);
lean_dec(v_conv_3915_);
v_a_3945_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3925_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3925_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(lean_object* v_hUserName_3953_, lean_object* v_conv_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(v_hUserName_3953_, v_conv_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object* v_conv_3965_, lean_object* v_hUserName_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v___f_3976_; lean_object* v___x_3977_; 
v___f_3976_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3976_, 0, v_hUserName_3966_);
lean_closure_set(v___f_3976_, 1, v_conv_3965_);
v___x_3977_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3976_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object* v_conv_3978_, lean_object* v_hUserName_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v_conv_3978_, v_hUserName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3989_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7(void){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Array_mkArray0(lean_box(0));
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object* v_stx_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; uint8_t v___x_4061_; 
v___x_4020_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__0));
v___x_4021_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
lean_inc(v_stx_4010_);
v___x_4061_ = l_Lean_Syntax_isOfKind(v_stx_4010_, v___x_4021_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; 
lean_dec(v_stx_4010_);
v___x_4062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4062_;
}
else
{
lean_object* v___x_4063_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v_tk_4097_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___x_4125_; lean_object* v_loc_x3f_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4063_ = lean_unsigned_to_nat(0u);
v_tk_4097_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4063_);
v___x_4125_ = lean_unsigned_to_nat(1u);
v___x_4189_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4125_);
v___x_4190_ = l_Lean_Syntax_isNone(v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4191_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4189_);
v___x_4192_ = l_Lean_Syntax_matchesNull(v___x_4189_, v___x_4191_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
lean_dec(v___x_4189_);
lean_dec(v_tk_4097_);
lean_dec(v_stx_4010_);
v___x_4193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4193_;
}
else
{
lean_object* v_loc_x3f_4194_; lean_object* v___x_4195_; 
v_loc_x3f_4194_ = l_Lean_Syntax_getArg(v___x_4189_, v___x_4125_);
lean_dec(v___x_4189_);
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v_loc_x3f_4194_);
v_loc_x3f_4127_ = v___x_4195_;
v___y_4128_ = v_a_4011_;
v___y_4129_ = v_a_4012_;
v___y_4130_ = v_a_4013_;
v___y_4131_ = v_a_4014_;
v___y_4132_ = v_a_4015_;
v___y_4133_ = v_a_4016_;
v___y_4134_ = v_a_4017_;
v___y_4135_ = v_a_4018_;
goto v___jp_4126_;
}
}
else
{
lean_object* v___x_4196_; 
lean_dec(v___x_4189_);
v___x_4196_ = lean_box(0);
v_loc_x3f_4127_ = v___x_4196_;
v___y_4128_ = v_a_4011_;
v___y_4129_ = v_a_4012_;
v___y_4130_ = v_a_4013_;
v___y_4131_ = v_a_4014_;
v___y_4132_ = v_a_4015_;
v___y_4133_ = v_a_4016_;
v___y_4134_ = v_a_4017_;
v___y_4135_ = v_a_4018_;
goto v___jp_4126_;
}
v___jp_4064_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_inc_ref_n(v___y_4077_, 2);
v___x_4083_ = l_Array_append___redArg(v___y_4077_, v___y_4082_);
lean_dec_ref(v___y_4082_);
lean_inc_n(v___y_4074_, 2);
lean_inc_n(v___y_4069_, 3);
v___x_4084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4084_, 0, v___y_4069_);
lean_ctor_set(v___x_4084_, 1, v___y_4074_);
lean_ctor_set(v___x_4084_, 2, v___x_4083_);
v___x_4085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4085_, 0, v___y_4069_);
lean_ctor_set(v___x_4085_, 1, v___y_4074_);
lean_ctor_set(v___x_4085_, 2, v___y_4077_);
v___x_4086_ = l_Lean_SourceInfo_fromRef(v___y_4068_, v___x_4061_);
lean_dec(v___y_4068_);
v___x_4087_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__3));
v___x_4088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_4090_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__4));
v___x_4091_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__5));
v___x_4092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___y_4069_);
lean_ctor_set(v___x_4092_, 1, v___x_4090_);
if (lean_obj_tag(v___y_4080_) == 0)
{
lean_object* v___x_4093_; 
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4023_ = v___y_4065_;
v___y_4024_ = v___y_4066_;
v___y_4025_ = v___x_4092_;
v___y_4026_ = v___x_4088_;
v___y_4027_ = v___y_4067_;
v___y_4028_ = v___y_4069_;
v___y_4029_ = v___y_4070_;
v___y_4030_ = v___y_4071_;
v___y_4031_ = v___y_4072_;
v___y_4032_ = v___x_4084_;
v___y_4033_ = v___y_4073_;
v___y_4034_ = v___y_4074_;
v___y_4035_ = v___y_4075_;
v___y_4036_ = v___y_4076_;
v___y_4037_ = v___x_4085_;
v___y_4038_ = v___y_4077_;
v___y_4039_ = v___y_4078_;
v___y_4040_ = v___x_4091_;
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4081_;
v___y_4043_ = v___x_4089_;
v___y_4044_ = v___x_4093_;
goto v___jp_4022_;
}
else
{
lean_object* v_val_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_val_4094_ = lean_ctor_get(v___y_4080_, 0);
lean_inc(v_val_4094_);
lean_dec_ref(v___y_4080_);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___x_4096_ = lean_array_push(v___x_4095_, v_val_4094_);
v___y_4023_ = v___y_4065_;
v___y_4024_ = v___y_4066_;
v___y_4025_ = v___x_4092_;
v___y_4026_ = v___x_4088_;
v___y_4027_ = v___y_4067_;
v___y_4028_ = v___y_4069_;
v___y_4029_ = v___y_4070_;
v___y_4030_ = v___y_4071_;
v___y_4031_ = v___y_4072_;
v___y_4032_ = v___x_4084_;
v___y_4033_ = v___y_4073_;
v___y_4034_ = v___y_4074_;
v___y_4035_ = v___y_4075_;
v___y_4036_ = v___y_4076_;
v___y_4037_ = v___x_4085_;
v___y_4038_ = v___y_4077_;
v___y_4039_ = v___y_4078_;
v___y_4040_ = v___x_4091_;
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4081_;
v___y_4043_ = v___x_4089_;
v___y_4044_ = v___x_4096_;
goto v___jp_4022_;
}
}
v___jp_4098_:
{
lean_object* v_ref_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_ref_4113_ = lean_ctor_get(v___y_4105_, 5);
v___x_4114_ = 0;
v___x_4115_ = l_Lean_SourceInfo_fromRef(v_ref_4113_, v___x_4114_);
v___x_4116_ = l_Lean_SourceInfo_fromRef(v_tk_4097_, v___x_4061_);
lean_dec(v_tk_4097_);
v___x_4117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
lean_ctor_set(v___x_4117_, 1, v___x_4020_);
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4119_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalConv___closed__7, &l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once, _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7);
if (lean_obj_tag(v___y_4108_) == 1)
{
lean_object* v_val_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_val_4120_ = lean_ctor_get(v___y_4108_, 0);
lean_inc(v_val_4120_);
lean_dec_ref(v___y_4108_);
v___x_4121_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__8));
lean_inc(v___x_4115_);
v___x_4122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4115_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Array_mkArray2___redArg(v___x_4122_, v_val_4120_);
v___y_4065_ = v___y_4099_;
v___y_4066_ = v___y_4100_;
v___y_4067_ = v___y_4101_;
v___y_4068_ = v___y_4102_;
v___y_4069_ = v___x_4115_;
v___y_4070_ = v___y_4103_;
v___y_4071_ = v___y_4104_;
v___y_4072_ = v___x_4117_;
v___y_4073_ = v___y_4105_;
v___y_4074_ = v___x_4118_;
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___y_4107_;
v___y_4077_ = v___x_4119_;
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4110_;
v___y_4080_ = v___y_4112_;
v___y_4081_ = v___y_4111_;
v___y_4082_ = v___x_4123_;
goto v___jp_4064_;
}
else
{
lean_object* v___x_4124_; 
lean_dec(v___y_4108_);
v___x_4124_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4065_ = v___y_4099_;
v___y_4066_ = v___y_4100_;
v___y_4067_ = v___y_4101_;
v___y_4068_ = v___y_4102_;
v___y_4069_ = v___x_4115_;
v___y_4070_ = v___y_4103_;
v___y_4071_ = v___y_4104_;
v___y_4072_ = v___x_4117_;
v___y_4073_ = v___y_4105_;
v___y_4074_ = v___x_4118_;
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___y_4107_;
v___y_4077_ = v___x_4119_;
v___y_4078_ = v___y_4109_;
v___y_4079_ = v___y_4110_;
v___y_4080_ = v___y_4112_;
v___y_4081_ = v___y_4111_;
v___y_4082_ = v___x_4124_;
goto v___jp_4064_;
}
}
v___jp_4126_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4136_ = lean_unsigned_to_nat(2u);
v___x_4137_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4136_);
v___x_4138_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4137_);
v___x_4139_ = l_Lean_Syntax_matchesNull(v___x_4137_, v___x_4138_);
if (v___x_4139_ == 0)
{
uint8_t v___x_4140_; 
v___x_4140_ = l_Lean_Syntax_matchesNull(v___x_4137_, v___x_4063_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_dec(v_loc_x3f_4127_);
lean_dec(v_tk_4097_);
lean_dec(v_stx_4010_);
v___x_4141_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4141_;
}
else
{
lean_object* v_fileName_4142_; lean_object* v_fileMap_4143_; lean_object* v_options_4144_; lean_object* v_currRecDepth_4145_; lean_object* v_maxRecDepth_4146_; lean_object* v_ref_4147_; lean_object* v_currNamespace_4148_; lean_object* v_openDecls_4149_; lean_object* v_initHeartbeats_4150_; lean_object* v_maxHeartbeats_4151_; lean_object* v_quotContext_4152_; lean_object* v_currMacroScope_4153_; uint8_t v_diag_4154_; lean_object* v_cancelTk_x3f_4155_; uint8_t v_suppressElabErrors_4156_; lean_object* v_inheritedTraceOptions_4157_; lean_object* v_arr_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_ref_4167_; lean_object* v___x_4168_; 
v_fileName_4142_ = lean_ctor_get(v___y_4134_, 0);
v_fileMap_4143_ = lean_ctor_get(v___y_4134_, 1);
v_options_4144_ = lean_ctor_get(v___y_4134_, 2);
v_currRecDepth_4145_ = lean_ctor_get(v___y_4134_, 3);
v_maxRecDepth_4146_ = lean_ctor_get(v___y_4134_, 4);
v_ref_4147_ = lean_ctor_get(v___y_4134_, 5);
v_currNamespace_4148_ = lean_ctor_get(v___y_4134_, 6);
v_openDecls_4149_ = lean_ctor_get(v___y_4134_, 7);
v_initHeartbeats_4150_ = lean_ctor_get(v___y_4134_, 8);
v_maxHeartbeats_4151_ = lean_ctor_get(v___y_4134_, 9);
v_quotContext_4152_ = lean_ctor_get(v___y_4134_, 10);
v_currMacroScope_4153_ = lean_ctor_get(v___y_4134_, 11);
v_diag_4154_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*14);
v_cancelTk_x3f_4155_ = lean_ctor_get(v___y_4134_, 12);
v_suppressElabErrors_4156_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4157_ = lean_ctor_get(v___y_4134_, 13);
v_arr_4158_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4138_);
v___x_4159_ = lean_unsigned_to_nat(4u);
v___x_4160_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4159_);
lean_dec(v_stx_4010_);
v___x_4161_ = lean_mk_empty_array_with_capacity(v___x_4136_);
v___x_4162_ = lean_array_push(v___x_4161_, v_tk_4097_);
v___x_4163_ = lean_array_push(v___x_4162_, v_arr_4158_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4165_ = lean_box(2);
v___x_4166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v___x_4164_);
lean_ctor_set(v___x_4166_, 2, v___x_4163_);
v_ref_4167_ = l_Lean_replaceRef(v___x_4166_, v_ref_4147_);
lean_dec_ref(v___x_4166_);
lean_inc_ref(v_inheritedTraceOptions_4157_);
lean_inc(v_cancelTk_x3f_4155_);
lean_inc(v_currMacroScope_4153_);
lean_inc(v_quotContext_4152_);
lean_inc(v_maxHeartbeats_4151_);
lean_inc(v_initHeartbeats_4150_);
lean_inc(v_openDecls_4149_);
lean_inc(v_currNamespace_4148_);
lean_inc(v_maxRecDepth_4146_);
lean_inc(v_currRecDepth_4145_);
lean_inc_ref(v_options_4144_);
lean_inc_ref(v_fileMap_4143_);
lean_inc_ref(v_fileName_4142_);
v___x_4168_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4168_, 0, v_fileName_4142_);
lean_ctor_set(v___x_4168_, 1, v_fileMap_4143_);
lean_ctor_set(v___x_4168_, 2, v_options_4144_);
lean_ctor_set(v___x_4168_, 3, v_currRecDepth_4145_);
lean_ctor_set(v___x_4168_, 4, v_maxRecDepth_4146_);
lean_ctor_set(v___x_4168_, 5, v_ref_4167_);
lean_ctor_set(v___x_4168_, 6, v_currNamespace_4148_);
lean_ctor_set(v___x_4168_, 7, v_openDecls_4149_);
lean_ctor_set(v___x_4168_, 8, v_initHeartbeats_4150_);
lean_ctor_set(v___x_4168_, 9, v_maxHeartbeats_4151_);
lean_ctor_set(v___x_4168_, 10, v_quotContext_4152_);
lean_ctor_set(v___x_4168_, 11, v_currMacroScope_4153_);
lean_ctor_set(v___x_4168_, 12, v_cancelTk_x3f_4155_);
lean_ctor_set(v___x_4168_, 13, v_inheritedTraceOptions_4157_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*14, v_diag_4154_);
lean_ctor_set_uint8(v___x_4168_, sizeof(void*)*14 + 1, v_suppressElabErrors_4156_);
if (lean_obj_tag(v_loc_x3f_4127_) == 1)
{
lean_object* v_val_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_val_4169_ = lean_ctor_get(v_loc_x3f_4127_, 0);
lean_inc(v_val_4169_);
lean_dec_ref(v_loc_x3f_4127_);
v___x_4170_ = l_Lean_TSyntax_getId(v_val_4169_);
lean_dec(v_val_4169_);
v___x_4171_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v___x_4160_, v___x_4170_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___x_4168_, v___y_4135_);
lean_dec_ref(v___x_4168_);
return v___x_4171_;
}
else
{
lean_object* v___x_4172_; 
lean_dec(v_loc_x3f_4127_);
v___x_4172_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v___x_4160_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___x_4168_, v___y_4135_);
lean_dec_ref(v___x_4168_);
return v___x_4172_;
}
}
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v_arr_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4173_ = l_Lean_Syntax_getArg(v___x_4137_, v___x_4125_);
v___x_4174_ = l_Lean_Syntax_getArg(v___x_4137_, v___x_4136_);
lean_dec(v___x_4137_);
v_arr_4175_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4138_);
v___x_4176_ = lean_unsigned_to_nat(4u);
v___x_4177_ = l_Lean_Syntax_getArg(v_stx_4010_, v___x_4176_);
lean_dec(v_stx_4010_);
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_4179_ = l_Lean_Syntax_getOptional_x3f(v___x_4173_);
lean_dec(v___x_4173_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_box(0);
v___y_4099_ = v___y_4129_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___x_4174_;
v___y_4102_ = v_arr_4175_;
v___y_4103_ = v___y_4135_;
v___y_4104_ = v___x_4178_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___x_4177_;
v___y_4108_ = v_loc_x3f_4127_;
v___y_4109_ = v___y_4130_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___x_4180_;
goto v___jp_4098_;
}
else
{
lean_object* v_val_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
v_val_4181_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4179_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_val_4181_);
lean_dec(v___x_4179_);
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
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_val_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
v___y_4099_ = v___y_4129_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___x_4174_;
v___y_4102_ = v_arr_4175_;
v___y_4103_ = v___y_4135_;
v___y_4104_ = v___x_4178_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___x_4177_;
v___y_4108_ = v_loc_x3f_4127_;
v___y_4109_ = v___y_4130_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___x_4186_;
goto v___jp_4098_;
}
}
}
}
}
}
v___jp_4022_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_inc_ref(v___y_4038_);
v___x_4045_ = l_Array_append___redArg(v___y_4038_, v___y_4044_);
lean_dec_ref(v___y_4044_);
lean_inc_n(v___y_4034_, 2);
lean_inc_n(v___y_4028_, 9);
v___x_4046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4046_, 0, v___y_4028_);
lean_ctor_set(v___x_4046_, 1, v___y_4034_);
lean_ctor_set(v___x_4046_, 2, v___x_4045_);
lean_inc(v___y_4040_);
v___x_4047_ = l_Lean_Syntax_node3(v___y_4028_, v___y_4040_, v___y_4025_, v___x_4046_, v___y_4027_);
v___x_4048_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__2));
v___x_4049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___y_4028_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
v___x_4050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_4051_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_4052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___y_4028_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_4054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___y_4028_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_Syntax_node3(v___y_4028_, v___x_4050_, v___x_4052_, v___y_4036_, v___x_4054_);
v___x_4056_ = l_Lean_Syntax_node3(v___y_4028_, v___y_4034_, v___x_4047_, v___x_4049_, v___x_4055_);
lean_inc(v___y_4043_);
v___x_4057_ = l_Lean_Syntax_node1(v___y_4028_, v___y_4043_, v___x_4056_);
lean_inc(v___y_4030_);
v___x_4058_ = l_Lean_Syntax_node1(v___y_4028_, v___y_4030_, v___x_4057_);
v___x_4059_ = l_Lean_Syntax_node5(v___y_4028_, v___x_4021_, v___y_4031_, v___y_4032_, v___y_4037_, v___y_4026_, v___x_4058_);
v___x_4060_ = l_Lean_Elab_Tactic_evalTactic(v___x_4059_, v___y_4024_, v___y_4023_, v___y_4039_, v___y_4041_, v___y_4035_, v___y_4042_, v___y_4033_, v___y_4029_);
return v___x_4060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object* v_stx_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Elab_Tactic_Conv_evalConv(v_stx_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4216_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4217_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
v___x_4218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4219_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConv___boxed), 10, 0);
v___x_4220_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4216_, v___x_4217_, v___x_4218_, v___x_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3(){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6));
v___x_4251_ = l_Lean_addBuiltinDeclarationRanges(v___x_4249_, v___x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object* v_a_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Elab_Tactic_evalFirst(v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_Elab_Tactic_Conv_evalFirst(v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(){
_start:
{
lean_object* v___f_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___f_4292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0));
v___x_4293_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2));
v___x_4295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4296_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4293_, v___x_4294_, v___x_4295_, v___f_4292_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3(){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6));
v___x_4327_ = l_Lean_addBuiltinDeclarationRanges(v___x_4325_, v___x_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
return v_res_4329_;
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
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
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
