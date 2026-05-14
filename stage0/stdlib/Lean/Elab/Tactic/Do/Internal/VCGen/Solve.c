// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Solve
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails public import Lean.Meta.Sym.InstantiateS
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_letName_x21(lean_object*);
lean_object* l_Lean_Expr_letBody_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letValue_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "foralls in `solve`"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-intro: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__5_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "let-zeta-dup: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "mvcgen': shared-continuation handling for `__do_jp` is not yet implemented. Detection point reached at "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 205, .m_capacity = 205, .m_length = 204, .m_data = "; the upstream `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) needs to be ported to the worklist style. Drop `(jp := true)` to fall back to the default zeta-unfold behaviour."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Applying "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "entails_cons_intro"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 192, 217, 126, 138, 217, 120, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " failed. It should not."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 60, 94, 227, 159, 215, 186, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Solved by rfl "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Trying rfl "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-hoist: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "split rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to apply split rule for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fvar-zeta: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "spec rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to apply rule "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Needed state intro. Retrying."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Rule type: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Spec for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Applying a spec for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ". Excess args: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PredTrans"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 249, 197, 27, 172, 11, 117, 203)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(196, 51, 114, 249, 35, 73, 112, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(209, 91, 166, 6, 71, 210, 197, 93)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(111, 2, 24, 48, 222, 174, 4, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 11, .m_data = "📜 Program: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 10, .m_data = "🎯 Target: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(v_x_7_);
lean_dec_ref(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
switch(lean_obj_tag(v_t_9_))
{
case 3:
{
lean_object* v_e_11_; lean_object* v_monad_12_; lean_object* v_thms_13_; lean_object* v___x_14_; 
v_e_11_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_e_11_);
v_monad_12_ = lean_ctor_get(v_t_9_, 1);
lean_inc_ref(v_monad_12_);
v_thms_13_ = lean_ctor_get(v_t_9_, 2);
lean_inc_ref(v_thms_13_);
lean_dec_ref(v_t_9_);
v___x_14_ = lean_apply_3(v_k_10_, v_e_11_, v_monad_12_, v_thms_13_);
return v___x_14_;
}
case 4:
{
lean_object* v_subgoals_15_; lean_object* v___x_16_; 
v_subgoals_15_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_subgoals_15_);
lean_dec_ref(v_t_9_);
v___x_16_ = lean_apply_1(v_k_10_, v_subgoals_15_);
return v___x_16_;
}
default: 
{
lean_object* v_target_17_; lean_object* v___x_18_; 
v_target_17_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_target_17_);
lean_dec_ref(v_t_9_);
v___x_18_ = lean_apply_1(v_k_10_, v_target_17_);
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim___redArg(lean_object* v_t_31_, lean_object* v_noEntailment_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_31_, v_noEntailment_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noEntailment_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_noEntailment_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_35_, v_noEntailment_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim___redArg(lean_object* v_t_39_, lean_object* v_noProgramFoundInTarget_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_39_, v_noProgramFoundInTarget_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noProgramFoundInTarget_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_noProgramFoundInTarget_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_43_, v_noProgramFoundInTarget_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim___redArg(lean_object* v_t_47_, lean_object* v_noStrategyForProgram_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_47_, v_noStrategyForProgram_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noStrategyForProgram_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_noStrategyForProgram_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_51_, v_noStrategyForProgram_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim___redArg(lean_object* v_t_55_, lean_object* v_noSpecFoundForProgram_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_55_, v_noSpecFoundForProgram_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_noSpecFoundForProgram_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_noSpecFoundForProgram_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_59_, v_noSpecFoundForProgram_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(lean_object* v_t_63_, lean_object* v_goals_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_63_, v_goals_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_goals_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_67_, v_goals_69_);
return v___x_70_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(lean_object* v_e_76_){
_start:
{
switch(lean_obj_tag(v_e_76_))
{
case 5:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2));
v___x_78_ = l_Lean_Expr_isAppOf(v_e_76_, v___x_77_);
return v___x_78_;
}
case 6:
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
case 7:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
case 8:
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
case 10:
{
lean_object* v_expr_82_; 
v_expr_82_ = lean_ctor_get(v_e_76_, 1);
v_e_76_ = v_expr_82_;
goto _start;
}
case 11:
{
lean_object* v_struct_84_; 
v_struct_84_ = lean_ctor_get(v_e_76_, 2);
v_e_76_ = v_struct_84_;
goto _start;
}
default: 
{
uint8_t v___x_86_; 
v___x_86_ = 1;
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___boxed(lean_object* v_e_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_e_87_);
lean_dec_ref(v_e_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__0));
v___x_92_ = l_Lean_stringToMessageData(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(lean_object* v_goal_93_, lean_object* v_target_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_Lean_Expr_isForall(v_target_94_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_goal_93_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___closed__1);
v___x_108_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_goal_93_, v___x_107_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v_a_109_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_116_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_108_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_108_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg___boxed(lean_object* v_goal_129_, lean_object* v_target_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_129_, v_target_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec_ref(v_target_130_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(lean_object* v_goal_141_, lean_object* v_target_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_141_, v_target_142_, v_a_143_, v_a_144_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___boxed(lean_object* v_goal_156_, lean_object* v_target_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro(v_goal_156_, v_target_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec_ref(v_target_157_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; lean_object* v_env_178_; lean_object* v___x_179_; lean_object* v_mctx_180_; lean_object* v_lctx_181_; lean_object* v_options_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_177_ = lean_st_ref_get(v___y_175_);
v_env_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_env_178_);
lean_dec(v___x_177_);
v___x_179_ = lean_st_ref_get(v___y_173_);
v_mctx_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_mctx_180_);
lean_dec(v___x_179_);
v_lctx_181_ = lean_ctor_get(v___y_172_, 2);
v_options_182_ = lean_ctor_get(v___y_174_, 2);
lean_inc_ref(v_options_182_);
lean_inc_ref(v_lctx_181_);
v___x_183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_183_, 0, v_env_178_);
lean_ctor_set(v___x_183_, 1, v_mctx_180_);
lean_ctor_set(v___x_183_, 2, v_lctx_181_);
lean_ctor_set(v___x_183_, 3, v_options_182_);
v___x_184_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_msgData_171_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0___boxed(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msgData_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_193_; double v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_float_of_nat(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(lean_object* v_cls_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_252_; 
v_ref_205_ = lean_ctor_get(v___y_202_, 5);
v___x_206_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_252_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_252_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_252_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v_traceState_212_; lean_object* v_env_213_; lean_object* v_nextMacroScope_214_; lean_object* v_ngen_215_; lean_object* v_auxDeclNGen_216_; lean_object* v_cache_217_; lean_object* v_messages_218_; lean_object* v_infoState_219_; lean_object* v_snapshotTasks_220_; lean_object* v_newDecls_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_251_; 
v___x_211_ = lean_st_ref_take(v___y_203_);
v_traceState_212_ = lean_ctor_get(v___x_211_, 4);
v_env_213_ = lean_ctor_get(v___x_211_, 0);
v_nextMacroScope_214_ = lean_ctor_get(v___x_211_, 1);
v_ngen_215_ = lean_ctor_get(v___x_211_, 2);
v_auxDeclNGen_216_ = lean_ctor_get(v___x_211_, 3);
v_cache_217_ = lean_ctor_get(v___x_211_, 5);
v_messages_218_ = lean_ctor_get(v___x_211_, 6);
v_infoState_219_ = lean_ctor_get(v___x_211_, 7);
v_snapshotTasks_220_ = lean_ctor_get(v___x_211_, 8);
v_newDecls_221_ = lean_ctor_get(v___x_211_, 9);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_251_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_newDecls_221_);
lean_inc(v_snapshotTasks_220_);
lean_inc(v_infoState_219_);
lean_inc(v_messages_218_);
lean_inc(v_cache_217_);
lean_inc(v_traceState_212_);
lean_inc(v_auxDeclNGen_216_);
lean_inc(v_ngen_215_);
lean_inc(v_nextMacroScope_214_);
lean_inc(v_env_213_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint64_t v_tid_225_; lean_object* v_traces_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_tid_225_ = lean_ctor_get_uint64(v_traceState_212_, sizeof(void*)*1);
v_traces_226_ = lean_ctor_get(v_traceState_212_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_traceState_212_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_traceState_212_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_traces_226_);
lean_dec(v_traceState_212_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; double v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0);
v___x_232_ = 0;
v___x_233_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1));
v___x_234_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_234_, 0, v_cls_198_);
lean_ctor_set(v___x_234_, 1, v___x_230_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_ctor_set_float(v___x_234_, sizeof(void*)*3, v___x_231_);
lean_ctor_set_float(v___x_234_, sizeof(void*)*3 + 8, v___x_231_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*3 + 16, v___x_232_);
v___x_235_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2));
v___x_236_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v_a_207_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_inc(v_ref_205_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_205_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_PersistentArray_push___redArg(v_traces_226_, v___x_237_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_238_);
v___x_240_ = v___x_228_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_238_);
lean_ctor_set_uint64(v_reuseFailAlloc_249_, sizeof(void*)*1, v_tid_225_);
v___x_240_ = v_reuseFailAlloc_249_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___x_240_);
v___x_242_ = v___x_223_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_env_213_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_nextMacroScope_214_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_ngen_215_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_auxDeclNGen_216_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_messages_218_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_infoState_219_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_snapshotTasks_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_newDecls_221_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_st_ref_set(v___y_203_, v___x_242_);
v___x_244_ = lean_box(0);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_244_);
v___x_246_ = v___x_209_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___boxed(lean_object* v_cls_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_253_, v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_ref_267_; lean_object* v___x_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_ref_267_ = lean_ctor_get(v___y_264_, 5);
v___x_268_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_ref_267_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_267_);
lean_ctor_set(v___x_273_, 1, v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 1);
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg___boxed(lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
v___x_302_ = l_Lean_Name_append(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(lean_object* v_goal_312_, lean_object* v_target_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; uint8_t v___x_454_; 
v___x_454_ = l_Lean_Expr_isLet(v_target_313_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_goal_312_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
else
{
uint8_t v_useJP_457_; 
v_useJP_457_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*20 + 1);
if (v_useJP_457_ == 0)
{
v___y_403_ = v_a_314_;
v___y_404_ = v_a_315_;
v___y_405_ = v_a_316_;
v___y_406_ = v_a_317_;
v___y_407_ = v_a_318_;
v___y_408_ = v_a_319_;
v___y_409_ = v_a_320_;
v___y_410_ = v_a_321_;
v___y_411_ = v_a_322_;
v___y_412_ = v_a_323_;
v___y_413_ = v_a_324_;
goto v___jp_402_;
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = l_Lean_Expr_letName_x21(v_target_313_);
lean_inc(v___x_458_);
v___x_459_ = l_Lean_Elab_Tactic_Do_isJP(v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v___x_458_);
v___y_403_ = v_a_314_;
v___y_404_ = v_a_315_;
v___y_405_ = v_a_316_;
v___y_406_ = v_a_317_;
v___y_407_ = v_a_318_;
v___y_408_ = v_a_319_;
v___y_409_ = v_a_320_;
v___y_410_ = v_a_321_;
v___y_411_ = v_a_322_;
v___y_412_ = v_a_323_;
v___y_413_ = v_a_324_;
goto v___jp_402_;
}
else
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = l_Lean_Expr_letValue_x21(v_target_313_);
v___x_461_ = l_Lean_Expr_isLambda(v___x_460_);
lean_dec_ref(v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v___x_458_);
v___y_403_ = v_a_314_;
v___y_404_ = v_a_315_;
v___y_405_ = v_a_316_;
v___y_406_ = v_a_317_;
v___y_407_ = v_a_318_;
v___y_408_ = v_a_319_;
v___y_409_ = v_a_320_;
v___y_410_ = v_a_321_;
v___y_411_ = v_a_322_;
v___y_412_ = v_a_323_;
v___y_413_ = v_a_324_;
goto v___jp_402_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_goal_312_);
v___x_462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13);
v___x_463_ = l_Lean_MessageData_ofName(v___x_458_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_466_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
v___jp_326_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
v___x_336_ = l_Lean_Expr_letName_x21(v_target_313_);
v___x_337_ = l_Lean_MessageData_ofName(v___x_336_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_goal_312_, v___x_338_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_351_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_351_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_351_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v_a_340_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_347_);
v___x_349_ = v___x_342_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_339_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_339_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
v___jp_360_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = l_Lean_Expr_letBody_x21(v_target_313_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_368_);
v___x_370_ = lean_array_push(v___x_369_, v___y_361_);
v___x_371_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v___x_367_, v___x_370_, v___y_362_);
lean_dec_ref(v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v___x_373_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_312_, v_a_372_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_385_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_385_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v_a_374_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_381_);
v___x_383_ = v___x_376_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_373_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_goal_312_);
v_a_394_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_371_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_371_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
v___jp_402_:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = l_Lean_Expr_letValue_x21(v_target_313_);
v___x_415_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v_options_416_; uint8_t v_hasTrace_417_; 
lean_dec_ref(v___x_414_);
v_options_416_ = lean_ctor_get(v___y_412_, 2);
v_hasTrace_417_ = lean_ctor_get_uint8(v_options_416_, sizeof(void*)*1);
if (v_hasTrace_417_ == 0)
{
v___y_327_ = v___y_403_;
v___y_328_ = v___y_404_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
v___y_334_ = v___y_413_;
goto v___jp_326_;
}
else
{
lean_object* v_inheritedTraceOptions_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_inheritedTraceOptions_418_ = lean_ctor_get(v___y_412_, 13);
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_418_, v_options_416_, v___x_420_);
if (v___x_421_ == 0)
{
v___y_327_ = v___y_403_;
v___y_328_ = v___y_404_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
v___y_334_ = v___y_413_;
goto v___jp_326_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
v___x_423_ = l_Lean_Expr_letName_x21(v_target_313_);
v___x_424_ = l_Lean_MessageData_ofName(v___x_423_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_419_, v___x_425_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_dec_ref(v___x_426_);
v___y_327_ = v___y_403_;
v___y_328_ = v___y_404_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
v___y_334_ = v___y_413_;
goto v___jp_326_;
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_goal_312_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
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
lean_object* v_options_435_; uint8_t v_hasTrace_436_; 
v_options_435_ = lean_ctor_get(v___y_412_, 2);
v_hasTrace_436_ = lean_ctor_get_uint8(v_options_435_, sizeof(void*)*1);
if (v_hasTrace_436_ == 0)
{
v___y_361_ = v___x_414_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
v___y_366_ = v___y_413_;
goto v___jp_360_;
}
else
{
lean_object* v_inheritedTraceOptions_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_inheritedTraceOptions_437_ = lean_ctor_get(v___y_412_, 13);
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_439_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_440_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_437_, v_options_435_, v___x_439_);
if (v___x_440_ == 0)
{
v___y_361_ = v___x_414_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
v___y_366_ = v___y_413_;
goto v___jp_360_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11);
v___x_442_ = l_Lean_Expr_letName_x21(v_target_313_);
v___x_443_ = l_Lean_MessageData_ofName(v___x_442_);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_441_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_438_, v___x_444_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_dec_ref(v___x_445_);
v___y_361_ = v___x_414_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
v___y_366_ = v___y_413_;
goto v___jp_360_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___x_414_);
lean_dec(v_goal_312_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___boxed(lean_object* v_goal_476_, lean_object* v_target_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_476_, v_target_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec_ref(v_target_477_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(lean_object* v_cls_491_, lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_491_, v_msg_492_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___boxed(lean_object* v_cls_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(v_cls_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(lean_object* v_00_u03b1_521_, lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_522_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___boxed(lean_object* v_00_u03b1_536_, lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(v_00_u03b1_536_, v_msg_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(lean_object* v_goal_557_, lean_object* v_target_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = l_Lean_Expr_getAppFn(v_target_558_);
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2));
v___x_573_ = l_Lean_Expr_isConstOf(v___x_571_, v___x_572_);
lean_dec_ref(v___x_571_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_goal_557_);
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(v_goal_557_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_588_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_588_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_588_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_588_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v_a_577_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_576_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_576_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___boxed(lean_object* v_goal_597_, lean_object* v_target_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_597_, v_target_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec_ref(v_target_598_);
return v_res_611_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5(void){
_start:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 0;
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4));
v___x_624_ = l_Lean_MessageData_ofConstName(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5);
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8);
v___x_632_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(lean_object* v_goal_637_, lean_object* v_T_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_isLambda(v_T_638_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_goal_637_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
else
{
lean_object* v_entailsConsIntroRule_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_entailsConsIntroRule_654_ = lean_ctor_get(v_a_639_, 1);
v___x_655_ = lean_box(0);
lean_inc(v_goal_637_);
lean_inc_ref(v_entailsConsIntroRule_654_);
v___x_656_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsConsIntroRule_654_, v_goal_637_, v___x_655_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_695_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_695_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_695_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_695_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; 
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_mvarIds_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_mvarIds_682_ = lean_ctor_get(v_a_657_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v_a_657_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_mvarIds_682_);
lean_dec(v_a_657_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
if (lean_obj_tag(v_mvarIds_682_) == 1)
{
lean_object* v_tail_686_; 
v_tail_686_ = lean_ctor_get(v_mvarIds_682_, 1);
if (lean_obj_tag(v_tail_686_) == 0)
{
lean_object* v___x_688_; 
lean_dec(v_goal_637_);
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 4);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_mvarIds_682_);
v___x_688_ = v_reuseFailAlloc_693_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_689_);
v___x_691_ = v___x_659_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_dec_ref(v_mvarIds_682_);
lean_del_object(v___x_684_);
lean_del_object(v___x_659_);
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
v___y_665_ = v_a_649_;
goto v___jp_661_;
}
}
else
{
lean_del_object(v___x_684_);
lean_dec(v_mvarIds_682_);
lean_del_object(v___x_659_);
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
v___y_665_ = v_a_649_;
goto v___jp_661_;
}
}
}
else
{
lean_del_object(v___x_659_);
lean_dec(v_a_657_);
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
v___y_665_ = v_a_649_;
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_MVarId_getType(v_goal_637_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9);
v___x_669_ = l_Lean_MessageData_ofExpr(v_a_667_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_672_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_673_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_666_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_666_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_goal_637_);
v_a_696_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_656_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_656_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___boxed(lean_object* v_goal_704_, lean_object* v_T_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_704_, v_T_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec_ref(v_T_705_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(lean_object* v_f_719_, lean_object* v_a_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___y_729_; lean_object* v___x_732_; uint8_t v_debug_733_; 
v___x_732_ = lean_st_ref_get(v___y_722_);
v_debug_733_ = lean_ctor_get_uint8(v___x_732_, sizeof(void*)*10);
lean_dec(v___x_732_);
if (v_debug_733_ == 0)
{
v___y_729_ = v___y_722_;
goto v___jp_728_;
}
else
{
lean_object* v___x_734_; 
lean_inc_ref(v_f_719_);
v___x_734_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_719_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; 
lean_dec_ref(v___x_734_);
lean_inc_ref(v_a_720_);
v___x_735_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec_ref(v___x_735_);
v___y_729_ = v___y_722_;
goto v___jp_728_;
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_a_720_);
lean_dec_ref(v_f_719_);
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_a_720_);
lean_dec_ref(v_f_719_);
v_a_744_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_734_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_734_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = l_Lean_Expr_app___override(v_f_719_, v_a_720_);
v___x_731_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_730_, v___y_729_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg___boxed(lean_object* v_f_752_, lean_object* v_a_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_752_, v_a_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(lean_object* v_f_762_, lean_object* v_a_u2081_763_, lean_object* v_a_u2082_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_762_, v_a_u2081_763_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref(v___x_777_);
v___x_779_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_778_, v_a_u2082_764_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_779_;
}
else
{
lean_dec_ref(v_a_u2082_764_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0___boxed(lean_object* v_f_780_, lean_object* v_a_u2081_781_, lean_object* v_a_u2082_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_780_, v_a_u2081_781_, v_a_u2082_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(lean_object* v_f_796_, lean_object* v_a_u2081_797_, lean_object* v_a_u2082_798_, lean_object* v_a_u2083_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_796_, v_a_u2081_797_, v_a_u2082_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_813_, v_a_u2083_799_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_814_;
}
else
{
lean_dec_ref(v_a_u2083_799_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0___boxed(lean_object* v_f_815_, lean_object* v_a_u2081_816_, lean_object* v_a_u2082_817_, lean_object* v_a_u2083_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_815_, v_a_u2081_816_, v_a_u2082_817_, v_a_u2083_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(lean_object* v_goal_832_, lean_object* v_ent_833_, lean_object* v_00_u03c3s_834_, lean_object* v_H_835_, lean_object* v_T_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; 
lean_inc_ref(v_H_835_);
v___x_849_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_H_835_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
lean_inc_ref(v_T_836_);
v___x_851_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_T_836_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_899_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_899_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_899_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_899_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_891_; 
if (lean_obj_tag(v_a_850_) == 0)
{
if (lean_obj_tag(v_a_852_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_897_; 
lean_dec_ref(v_T_836_);
lean_dec_ref(v_H_835_);
lean_dec_ref(v_00_u03c3s_834_);
lean_dec_ref(v_ent_833_);
lean_dec(v_goal_832_);
v___x_895_ = lean_box(0);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_895_);
v___x_897_ = v___x_854_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_del_object(v___x_854_);
goto v___jp_893_;
}
}
else
{
lean_del_object(v___x_854_);
goto v___jp_893_;
}
v___jp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_833_, v_00_u03c3s_834_, v___y_857_, v___y_858_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_832_, v_a_860_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_873_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v_a_862_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_869_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_861_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_861_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_goal_832_);
v_a_882_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_859_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_859_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_890_:
{
if (lean_obj_tag(v_a_852_) == 0)
{
v___y_857_ = v___y_891_;
v___y_858_ = v_T_836_;
goto v___jp_856_;
}
else
{
lean_object* v_val_892_; 
lean_dec_ref(v_T_836_);
v_val_892_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_val_892_);
lean_dec_ref(v_a_852_);
v___y_857_ = v___y_891_;
v___y_858_ = v_val_892_;
goto v___jp_856_;
}
}
v___jp_893_:
{
if (lean_obj_tag(v_a_850_) == 0)
{
v___y_891_ = v_H_835_;
goto v___jp_890_;
}
else
{
lean_object* v_val_894_; 
lean_dec_ref(v_H_835_);
v_val_894_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_val_894_);
lean_dec_ref(v_a_850_);
v___y_891_ = v_val_894_;
goto v___jp_890_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_850_);
lean_dec_ref(v_T_836_);
lean_dec_ref(v_H_835_);
lean_dec_ref(v_00_u03c3s_834_);
lean_dec_ref(v_ent_833_);
lean_dec(v_goal_832_);
v_a_900_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_851_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_851_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref(v_T_836_);
lean_dec_ref(v_H_835_);
lean_dec_ref(v_00_u03c3s_834_);
lean_dec_ref(v_ent_833_);
lean_dec(v_goal_832_);
v_a_908_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_849_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_849_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT___boxed(lean_object** _args){
lean_object* v_goal_916_ = _args[0];
lean_object* v_ent_917_ = _args[1];
lean_object* v_00_u03c3s_918_ = _args[2];
lean_object* v_H_919_ = _args[3];
lean_object* v_T_920_ = _args[4];
lean_object* v_a_921_ = _args[5];
lean_object* v_a_922_ = _args[6];
lean_object* v_a_923_ = _args[7];
lean_object* v_a_924_ = _args[8];
lean_object* v_a_925_ = _args[9];
lean_object* v_a_926_ = _args[10];
lean_object* v_a_927_ = _args[11];
lean_object* v_a_928_ = _args[12];
lean_object* v_a_929_ = _args[13];
lean_object* v_a_930_ = _args[14];
lean_object* v_a_931_ = _args[15];
lean_object* v_a_932_ = _args[16];
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_916_, v_ent_917_, v_00_u03c3s_918_, v_H_919_, v_T_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(lean_object* v_f_934_, lean_object* v_a_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_934_, v_a_935_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___boxed(lean_object* v_f_949_, lean_object* v_a_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(v_f_949_, v_a_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_ks_968_; lean_object* v_vs_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_993_; 
v_ks_968_ = lean_ctor_get(v_x_964_, 0);
v_vs_969_ = lean_ctor_get(v_x_964_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_993_ == 0)
{
v___x_971_ = v_x_964_;
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_vs_969_);
lean_inc(v_ks_968_);
lean_dec(v_x_964_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_993_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = lean_array_get_size(v_ks_968_);
v___x_974_ = lean_nat_dec_lt(v_x_965_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec(v_x_965_);
v___x_975_ = lean_array_push(v_ks_968_, v_x_966_);
v___x_976_ = lean_array_push(v_vs_969_, v_x_967_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_976_);
lean_ctor_set(v___x_971_, 0, v___x_975_);
v___x_978_ = v___x_971_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v_k_x27_980_; uint8_t v___x_981_; 
v_k_x27_980_ = lean_array_fget_borrowed(v_ks_968_, v_x_965_);
v___x_981_ = l_Lean_instBEqMVarId_beq(v_x_966_, v_k_x27_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
if (v_isShared_972_ == 0)
{
v___x_983_ = v___x_971_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_ks_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_vs_969_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_x_965_, v___x_984_);
lean_dec(v_x_965_);
v_x_964_ = v___x_983_;
v_x_965_ = v___x_985_;
goto _start;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_988_ = lean_array_fset(v_ks_968_, v_x_965_, v_x_966_);
v___x_989_ = lean_array_fset(v_vs_969_, v_x_965_, v_x_967_);
lean_dec(v_x_965_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_989_);
lean_ctor_set(v___x_971_, 0, v___x_988_);
v___x_991_ = v___x_971_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_994_, lean_object* v_k_995_, lean_object* v_v_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_994_, v___x_997_, v_k_995_, v_v_996_);
return v___x_998_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; 
v___x_999_ = ((size_t)5ULL);
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_shift_left(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1004_ = lean_usize_sub(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1006_, size_t v_x_1007_, size_t v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_es_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; lean_object* v_j_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_es_1011_ = lean_ctor_get(v_x_1006_, 0);
v___x_1012_ = ((size_t)5ULL);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1015_ = lean_usize_land(v_x_1007_, v___x_1014_);
v_j_1016_ = lean_usize_to_nat(v___x_1015_);
v___x_1017_ = lean_array_get_size(v_es_1011_);
v___x_1018_ = lean_nat_dec_lt(v_j_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_dec(v_j_1016_);
lean_dec(v_x_1010_);
lean_dec(v_x_1009_);
return v_x_1006_;
}
else
{
lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1055_; 
lean_inc_ref(v_es_1011_);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_x_1006_, 0);
lean_dec(v_unused_1056_);
v___x_1020_ = v_x_1006_;
v_isShared_1021_ = v_isSharedCheck_1055_;
goto v_resetjp_1019_;
}
else
{
lean_dec(v_x_1006_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1055_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_v_1022_; lean_object* v___x_1023_; lean_object* v_xs_x27_1024_; lean_object* v___y_1026_; 
v_v_1022_ = lean_array_fget(v_es_1011_, v_j_1016_);
v___x_1023_ = lean_box(0);
v_xs_x27_1024_ = lean_array_fset(v_es_1011_, v_j_1016_, v___x_1023_);
switch(lean_obj_tag(v_v_1022_))
{
case 0:
{
lean_object* v_key_1031_; lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1042_; 
v_key_1031_ = lean_ctor_get(v_v_1022_, 0);
v_val_1032_ = lean_ctor_get(v_v_1022_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_v_1022_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1034_ = v_v_1022_;
v_isShared_1035_ = v_isSharedCheck_1042_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_val_1032_);
lean_inc(v_key_1031_);
lean_dec(v_v_1022_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1042_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Lean_instBEqMVarId_beq(v_x_1009_, v_key_1031_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_del_object(v___x_1034_);
v___x_1037_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1031_, v_val_1032_, v_x_1009_, v_x_1010_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
v___y_1026_ = v___x_1038_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_val_1032_);
lean_dec(v_key_1031_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v_x_1010_);
lean_ctor_set(v___x_1034_, 0, v_x_1009_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_x_1009_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_x_1010_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
v___y_1026_ = v___x_1040_;
goto v___jp_1025_;
}
}
}
}
case 1:
{
lean_object* v_node_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1053_; 
v_node_1043_ = lean_ctor_get(v_v_1022_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_v_1022_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1045_ = v_v_1022_;
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_node_1043_);
lean_dec(v_v_1022_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1047_ = lean_usize_shift_right(v_x_1007_, v___x_1012_);
v___x_1048_ = lean_usize_add(v_x_1008_, v___x_1013_);
v___x_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_node_1043_, v___x_1047_, v___x_1048_, v_x_1009_, v_x_1010_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v___y_1026_ = v___x_1051_;
goto v___jp_1025_;
}
}
}
default: 
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_x_1009_);
lean_ctor_set(v___x_1054_, 1, v_x_1010_);
v___y_1026_ = v___x_1054_;
goto v___jp_1025_;
}
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_array_fset(v_xs_x27_1024_, v_j_1016_, v___y_1026_);
lean_dec(v_j_1016_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1027_);
v___x_1029_ = v___x_1020_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
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
}
else
{
lean_object* v_ks_1057_; lean_object* v_vs_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1078_; 
v_ks_1057_ = lean_ctor_get(v_x_1006_, 0);
v_vs_1058_ = lean_ctor_get(v_x_1006_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1060_ = v_x_1006_;
v_isShared_1061_ = v_isSharedCheck_1078_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_vs_1058_);
lean_inc(v_ks_1057_);
lean_dec(v_x_1006_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1078_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_ks_1057_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_vs_1058_);
v___x_1063_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v_newNode_1064_; uint8_t v___y_1066_; size_t v___x_1072_; uint8_t v___x_1073_; 
v_newNode_1064_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1063_, v_x_1009_, v_x_1010_);
v___x_1072_ = ((size_t)7ULL);
v___x_1073_ = lean_usize_dec_le(v___x_1072_, v_x_1008_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1064_);
v___x_1075_ = lean_unsigned_to_nat(4u);
v___x_1076_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
lean_dec(v___x_1074_);
v___y_1066_ = v___x_1076_;
goto v___jp_1065_;
}
else
{
v___y_1066_ = v___x_1073_;
goto v___jp_1065_;
}
v___jp_1065_:
{
if (v___y_1066_ == 0)
{
lean_object* v_ks_1067_; lean_object* v_vs_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_ks_1067_ = lean_ctor_get(v_newNode_1064_, 0);
lean_inc_ref(v_ks_1067_);
v_vs_1068_ = lean_ctor_get(v_newNode_1064_, 1);
lean_inc_ref(v_vs_1068_);
lean_dec_ref(v_newNode_1064_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1008_, v_ks_1067_, v_vs_1068_, v___x_1069_, v___x_1070_);
lean_dec_ref(v_vs_1068_);
lean_dec_ref(v_ks_1067_);
return v___x_1071_;
}
else
{
return v_newNode_1064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1079_, lean_object* v_keys_1080_, lean_object* v_vals_1081_, lean_object* v_i_1082_, lean_object* v_entries_1083_){
_start:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_array_get_size(v_keys_1080_);
v___x_1085_ = lean_nat_dec_lt(v_i_1082_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_i_1082_);
return v_entries_1083_;
}
else
{
lean_object* v_k_1086_; lean_object* v_v_1087_; uint64_t v___x_1088_; size_t v_h_1089_; size_t v___x_1090_; lean_object* v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v_h_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_k_1086_ = lean_array_fget_borrowed(v_keys_1080_, v_i_1082_);
v_v_1087_ = lean_array_fget_borrowed(v_vals_1081_, v_i_1082_);
v___x_1088_ = l_Lean_instHashableMVarId_hash(v_k_1086_);
v_h_1089_ = lean_uint64_to_usize(v___x_1088_);
v___x_1090_ = ((size_t)5ULL);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_sub(v_depth_1079_, v___x_1092_);
v___x_1094_ = lean_usize_mul(v___x_1090_, v___x_1093_);
v_h_1095_ = lean_usize_shift_right(v_h_1089_, v___x_1094_);
v___x_1096_ = lean_nat_add(v_i_1082_, v___x_1091_);
lean_dec(v_i_1082_);
lean_inc(v_v_1087_);
lean_inc(v_k_1086_);
v___x_1097_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_entries_1083_, v_h_1095_, v_depth_1079_, v_k_1086_, v_v_1087_);
v_i_1082_ = v___x_1096_;
v_entries_1083_ = v___x_1097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_i_1102_, lean_object* v_entries_1103_){
_start:
{
size_t v_depth_boxed_1104_; lean_object* v_res_1105_; 
v_depth_boxed_1104_ = lean_unbox_usize(v_depth_1099_);
lean_dec(v_depth_1099_);
v_res_1105_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1104_, v_keys_1100_, v_vals_1101_, v_i_1102_, v_entries_1103_);
lean_dec_ref(v_vals_1101_);
lean_dec_ref(v_keys_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
size_t v_x_28836__boxed_1111_; size_t v_x_28837__boxed_1112_; lean_object* v_res_1113_; 
v_x_28836__boxed_1111_ = lean_unbox_usize(v_x_1107_);
lean_dec(v_x_1107_);
v_x_28837__boxed_1112_ = lean_unbox_usize(v_x_1108_);
lean_dec(v_x_1108_);
v_res_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1106_, v_x_28836__boxed_1111_, v_x_28837__boxed_1112_, v_x_1109_, v_x_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
uint64_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = l_Lean_instHashableMVarId_hash(v_x_1115_);
v___x_1118_ = lean_uint64_to_usize(v___x_1117_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1114_, v___x_1118_, v___x_1119_, v_x_1115_, v_x_1116_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(lean_object* v_mvarId_1121_, lean_object* v_val_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v_mctx_1126_; lean_object* v_cache_1127_; lean_object* v_zetaDeltaFVarIds_1128_; lean_object* v_postponed_1129_; lean_object* v_diag_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1158_; 
v___x_1125_ = lean_st_ref_take(v___y_1123_);
v_mctx_1126_ = lean_ctor_get(v___x_1125_, 0);
v_cache_1127_ = lean_ctor_get(v___x_1125_, 1);
v_zetaDeltaFVarIds_1128_ = lean_ctor_get(v___x_1125_, 2);
v_postponed_1129_ = lean_ctor_get(v___x_1125_, 3);
v_diag_1130_ = lean_ctor_get(v___x_1125_, 4);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1132_ = v___x_1125_;
v_isShared_1133_ = v_isSharedCheck_1158_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_diag_1130_);
lean_inc(v_postponed_1129_);
lean_inc(v_zetaDeltaFVarIds_1128_);
lean_inc(v_cache_1127_);
lean_inc(v_mctx_1126_);
lean_dec(v___x_1125_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1158_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_depth_1134_; lean_object* v_levelAssignDepth_1135_; lean_object* v_lmvarCounter_1136_; lean_object* v_mvarCounter_1137_; lean_object* v_lDecls_1138_; lean_object* v_decls_1139_; lean_object* v_userNames_1140_; lean_object* v_lAssignment_1141_; lean_object* v_eAssignment_1142_; lean_object* v_dAssignment_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1157_; 
v_depth_1134_ = lean_ctor_get(v_mctx_1126_, 0);
v_levelAssignDepth_1135_ = lean_ctor_get(v_mctx_1126_, 1);
v_lmvarCounter_1136_ = lean_ctor_get(v_mctx_1126_, 2);
v_mvarCounter_1137_ = lean_ctor_get(v_mctx_1126_, 3);
v_lDecls_1138_ = lean_ctor_get(v_mctx_1126_, 4);
v_decls_1139_ = lean_ctor_get(v_mctx_1126_, 5);
v_userNames_1140_ = lean_ctor_get(v_mctx_1126_, 6);
v_lAssignment_1141_ = lean_ctor_get(v_mctx_1126_, 7);
v_eAssignment_1142_ = lean_ctor_get(v_mctx_1126_, 8);
v_dAssignment_1143_ = lean_ctor_get(v_mctx_1126_, 9);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_mctx_1126_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1145_ = v_mctx_1126_;
v_isShared_1146_ = v_isSharedCheck_1157_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_dAssignment_1143_);
lean_inc(v_eAssignment_1142_);
lean_inc(v_lAssignment_1141_);
lean_inc(v_userNames_1140_);
lean_inc(v_decls_1139_);
lean_inc(v_lDecls_1138_);
lean_inc(v_mvarCounter_1137_);
lean_inc(v_lmvarCounter_1136_);
lean_inc(v_levelAssignDepth_1135_);
lean_inc(v_depth_1134_);
lean_dec(v_mctx_1126_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1157_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(v_eAssignment_1142_, v_mvarId_1121_, v_val_1122_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 8, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_depth_1134_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_levelAssignDepth_1135_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_lmvarCounter_1136_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_mvarCounter_1137_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_lDecls_1138_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_decls_1139_);
lean_ctor_set(v_reuseFailAlloc_1156_, 6, v_userNames_1140_);
lean_ctor_set(v_reuseFailAlloc_1156_, 7, v_lAssignment_1141_);
lean_ctor_set(v_reuseFailAlloc_1156_, 8, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 9, v_dAssignment_1143_);
v___x_1149_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1149_);
v___x_1151_ = v___x_1132_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_cache_1127_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_zetaDeltaFVarIds_1128_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_postponed_1129_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_diag_1130_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_st_ref_set(v___y_1123_, v___x_1151_);
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg___boxed(lean_object* v_mvarId_1159_, lean_object* v_val_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_mvarId_1159_, v_val_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__3));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__6));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(lean_object* v_goal_1180_, lean_object* v_ent_1181_, lean_object* v_00_u03c3s_1182_, lean_object* v_H_1183_, lean_object* v_T_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_options_1197_; lean_object* v_inheritedTraceOptions_1198_; uint8_t v_hasTrace_1199_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v_cls_1227_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v_a_1241_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; 
v_options_1197_ = lean_ctor_get(v_a_1194_, 2);
v_inheritedTraceOptions_1198_ = lean_ctor_get(v_a_1194_, 13);
v_hasTrace_1199_ = lean_ctor_get_uint8(v_options_1197_, sizeof(void*)*1);
v_cls_1227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
if (v_hasTrace_1199_ == 0)
{
v___y_1290_ = v_a_1185_;
v___y_1291_ = v_a_1186_;
v___y_1292_ = v_a_1187_;
v___y_1293_ = v_a_1188_;
v___y_1294_ = v_a_1189_;
v___y_1295_ = v_a_1190_;
v___y_1296_ = v_a_1191_;
v___y_1297_ = v_a_1192_;
v___y_1298_ = v_a_1193_;
v___y_1299_ = v_a_1194_;
v___y_1300_ = v_a_1195_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1357_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1198_, v_options_1197_, v___x_1356_);
if (v___x_1357_ == 0)
{
v___y_1290_ = v_a_1185_;
v___y_1291_ = v_a_1186_;
v___y_1292_ = v_a_1187_;
v___y_1293_ = v_a_1188_;
v___y_1294_ = v_a_1189_;
v___y_1295_ = v_a_1190_;
v___y_1296_ = v_a_1191_;
v___y_1297_ = v_a_1192_;
v___y_1298_ = v_a_1193_;
v___y_1299_ = v_a_1194_;
v___y_1300_ = v_a_1195_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7);
lean_inc(v_goal_1180_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_goal_1180_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1227_, v___x_1360_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref(v___x_1361_);
v___y_1290_ = v_a_1185_;
v___y_1291_ = v_a_1186_;
v___y_1292_ = v_a_1187_;
v___y_1293_ = v_a_1188_;
v___y_1294_ = v_a_1189_;
v___y_1295_ = v_a_1190_;
v___y_1296_ = v_a_1191_;
v___y_1297_ = v_a_1192_;
v___y_1298_ = v_a_1193_;
v___y_1299_ = v_a_1194_;
v___y_1300_ = v_a_1195_;
goto v___jp_1289_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_T_1184_);
lean_dec_ref(v_H_1183_);
lean_dec_ref(v_00_u03c3s_1182_);
lean_dec(v_goal_1180_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
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
v___jp_1200_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2));
v___x_1214_ = l_Lean_Expr_constLevels_x21(v_ent_1181_);
v___x_1215_ = l_Lean_mkConst(v___x_1213_, v___x_1214_);
v___x_1216_ = l_Lean_mkAppB(v___x_1215_, v_00_u03c3s_1182_, v_H_1183_);
v___x_1217_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_goal_1180_, v___x_1216_, v___y_1210_);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1226_);
v___x_1219_ = v___x_1217_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v___x_1217_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
lean_inc(v___y_1201_);
v___x_1221_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1201_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
v___jp_1228_:
{
if (v_a_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_dec_ref(v_H_1183_);
lean_dec_ref(v_00_u03c3s_1182_);
v___x_1242_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(v_goal_1180_, v___y_1239_, v___y_1232_, v___y_1235_, v___y_1230_, v___y_1231_, v___y_1237_, v___y_1234_, v___y_1238_, v___y_1229_, v___y_1236_, v___y_1233_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1263_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
if (lean_obj_tag(v_a_1243_) == 1)
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_T_1184_);
v_val_1247_ = lean_ctor_get(v_a_1243_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_a_1243_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1249_ = v_a_1243_;
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v_a_1243_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1258_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_inc(v___y_1240_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_val_1247_);
lean_ctor_set(v___x_1251_, 1, v___y_1240_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 4);
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1253_);
v___x_1255_ = v___x_1245_;
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
lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec(v_a_1243_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_T_1184_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1259_);
v___x_1261_ = v___x_1245_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_T_1184_);
v_a_1264_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1242_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1242_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_options_1272_; uint8_t v_hasTrace_1273_; 
lean_dec_ref(v_T_1184_);
v_options_1272_ = lean_ctor_get(v___y_1236_, 2);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_options_1272_, sizeof(void*)*1);
if (v_hasTrace_1273_ == 0)
{
v___y_1201_ = v___y_1240_;
v___y_1202_ = v___y_1239_;
v___y_1203_ = v___y_1232_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___y_1237_;
v___y_1208_ = v___y_1234_;
v___y_1209_ = v___y_1238_;
v___y_1210_ = v___y_1229_;
v___y_1211_ = v___y_1236_;
v___y_1212_ = v___y_1233_;
goto v___jp_1200_;
}
else
{
lean_object* v_inheritedTraceOptions_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_inheritedTraceOptions_1274_ = lean_ctor_get(v___y_1236_, 13);
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1274_, v_options_1272_, v___x_1275_);
if (v___x_1276_ == 0)
{
v___y_1201_ = v___y_1240_;
v___y_1202_ = v___y_1239_;
v___y_1203_ = v___y_1232_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___y_1237_;
v___y_1208_ = v___y_1234_;
v___y_1209_ = v___y_1238_;
v___y_1210_ = v___y_1229_;
v___y_1211_ = v___y_1236_;
v___y_1212_ = v___y_1233_;
goto v___jp_1200_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4);
lean_inc(v_goal_1180_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_goal_1180_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1227_, v___x_1279_, v___y_1238_, v___y_1229_, v___y_1236_, v___y_1233_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_dec_ref(v___x_1280_);
v___y_1201_ = v___y_1240_;
v___y_1202_ = v___y_1239_;
v___y_1203_ = v___y_1232_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___y_1237_;
v___y_1208_ = v___y_1234_;
v___y_1209_ = v___y_1238_;
v___y_1210_ = v___y_1229_;
v___y_1211_ = v___y_1236_;
v___y_1212_ = v___y_1233_;
goto v___jp_1200_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_H_1183_);
lean_dec_ref(v_00_u03c3s_1182_);
lean_dec(v_goal_1180_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
v___jp_1289_:
{
lean_object* v___x_1301_; uint8_t v_foApprox_1302_; uint8_t v_ctxApprox_1303_; uint8_t v_quasiPatternApprox_1304_; uint8_t v_constApprox_1305_; uint8_t v_isDefEqStuckEx_1306_; uint8_t v_unificationHints_1307_; uint8_t v_proofIrrelevance_1308_; uint8_t v_offsetCnstrs_1309_; uint8_t v_transparency_1310_; uint8_t v_etaStruct_1311_; uint8_t v_univApprox_1312_; uint8_t v_iota_1313_; uint8_t v_beta_1314_; uint8_t v_proj_1315_; uint8_t v_zeta_1316_; uint8_t v_zetaDelta_1317_; uint8_t v_zetaUnused_1318_; uint8_t v_zetaHave_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1355_; 
v___x_1301_ = l_Lean_Meta_Context_config(v___y_1297_);
v_foApprox_1302_ = lean_ctor_get_uint8(v___x_1301_, 0);
v_ctxApprox_1303_ = lean_ctor_get_uint8(v___x_1301_, 1);
v_quasiPatternApprox_1304_ = lean_ctor_get_uint8(v___x_1301_, 2);
v_constApprox_1305_ = lean_ctor_get_uint8(v___x_1301_, 3);
v_isDefEqStuckEx_1306_ = lean_ctor_get_uint8(v___x_1301_, 4);
v_unificationHints_1307_ = lean_ctor_get_uint8(v___x_1301_, 5);
v_proofIrrelevance_1308_ = lean_ctor_get_uint8(v___x_1301_, 6);
v_offsetCnstrs_1309_ = lean_ctor_get_uint8(v___x_1301_, 8);
v_transparency_1310_ = lean_ctor_get_uint8(v___x_1301_, 9);
v_etaStruct_1311_ = lean_ctor_get_uint8(v___x_1301_, 10);
v_univApprox_1312_ = lean_ctor_get_uint8(v___x_1301_, 11);
v_iota_1313_ = lean_ctor_get_uint8(v___x_1301_, 12);
v_beta_1314_ = lean_ctor_get_uint8(v___x_1301_, 13);
v_proj_1315_ = lean_ctor_get_uint8(v___x_1301_, 14);
v_zeta_1316_ = lean_ctor_get_uint8(v___x_1301_, 15);
v_zetaDelta_1317_ = lean_ctor_get_uint8(v___x_1301_, 16);
v_zetaUnused_1318_ = lean_ctor_get_uint8(v___x_1301_, 17);
v_zetaHave_1319_ = lean_ctor_get_uint8(v___x_1301_, 18);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1321_ = v___x_1301_;
v_isShared_1322_ = v_isSharedCheck_1355_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v___x_1301_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1355_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
uint8_t v_trackZetaDelta_1323_; lean_object* v_zetaDeltaSet_1324_; lean_object* v_lctx_1325_; lean_object* v_localInstances_1326_; lean_object* v_defEqCtx_x3f_1327_; lean_object* v_synthPendingDepth_1328_; lean_object* v_canUnfold_x3f_1329_; uint8_t v_univApprox_1330_; uint8_t v_inTypeClassResolution_1331_; uint8_t v_cacheInferType_1332_; uint8_t v___x_1333_; lean_object* v___x_1335_; 
v_trackZetaDelta_1323_ = lean_ctor_get_uint8(v___y_1297_, sizeof(void*)*7);
v_zetaDeltaSet_1324_ = lean_ctor_get(v___y_1297_, 1);
v_lctx_1325_ = lean_ctor_get(v___y_1297_, 2);
v_localInstances_1326_ = lean_ctor_get(v___y_1297_, 3);
v_defEqCtx_x3f_1327_ = lean_ctor_get(v___y_1297_, 4);
v_synthPendingDepth_1328_ = lean_ctor_get(v___y_1297_, 5);
v_canUnfold_x3f_1329_ = lean_ctor_get(v___y_1297_, 6);
v_univApprox_1330_ = lean_ctor_get_uint8(v___y_1297_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1331_ = lean_ctor_get_uint8(v___y_1297_, sizeof(void*)*7 + 2);
v_cacheInferType_1332_ = lean_ctor_get_uint8(v___y_1297_, sizeof(void*)*7 + 3);
v___x_1333_ = 1;
if (v_isShared_1322_ == 0)
{
v___x_1335_ = v___x_1321_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 0, v_foApprox_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 1, v_ctxApprox_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 2, v_quasiPatternApprox_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 3, v_constApprox_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 4, v_isDefEqStuckEx_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 5, v_unificationHints_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 6, v_proofIrrelevance_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 8, v_offsetCnstrs_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 9, v_transparency_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 10, v_etaStruct_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 11, v_univApprox_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 12, v_iota_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 13, v_beta_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 14, v_proj_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 15, v_zeta_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 16, v_zetaDelta_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 17, v_zetaUnused_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 18, v_zetaHave_1319_);
v___x_1335_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
uint64_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_ctor_set_uint8(v___x_1335_, 7, v___x_1333_);
v___x_1336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1335_);
v___x_1337_ = lean_box(0);
v___x_1338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__5));
v___x_1339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1339_, 0, v___x_1335_);
lean_ctor_set_uint64(v___x_1339_, sizeof(void*)*1, v___x_1336_);
lean_inc(v_canUnfold_x3f_1329_);
lean_inc(v_synthPendingDepth_1328_);
lean_inc(v_defEqCtx_x3f_1327_);
lean_inc_ref(v_localInstances_1326_);
lean_inc_ref(v_lctx_1325_);
lean_inc(v_zetaDeltaSet_1324_);
v___x_1340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v_zetaDeltaSet_1324_);
lean_ctor_set(v___x_1340_, 2, v_lctx_1325_);
lean_ctor_set(v___x_1340_, 3, v_localInstances_1326_);
lean_ctor_set(v___x_1340_, 4, v_defEqCtx_x3f_1327_);
lean_ctor_set(v___x_1340_, 5, v_synthPendingDepth_1328_);
lean_ctor_set(v___x_1340_, 6, v_canUnfold_x3f_1329_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*7, v_trackZetaDelta_1323_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*7 + 1, v_univApprox_1330_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1331_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*7 + 3, v_cacheInferType_1332_);
lean_inc_ref(v_T_1184_);
lean_inc_ref(v_H_1183_);
v___x_1341_ = l_Lean_Meta_Sym_isDefEqS(v_H_1183_, v_T_1184_, v___x_1333_, v___x_1333_, v___x_1338_, v___x_1338_, v___y_1295_, v___y_1296_, v___x_1340_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec_ref(v___x_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; uint8_t v___x_1343_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_unbox(v_a_1342_);
lean_dec(v_a_1342_);
v___y_1229_ = v___y_1298_;
v___y_1230_ = v___y_1293_;
v___y_1231_ = v___y_1294_;
v___y_1232_ = v___y_1291_;
v___y_1233_ = v___y_1300_;
v___y_1234_ = v___y_1296_;
v___y_1235_ = v___y_1292_;
v___y_1236_ = v___y_1299_;
v___y_1237_ = v___y_1295_;
v___y_1238_ = v___y_1297_;
v___y_1239_ = v___y_1290_;
v___y_1240_ = v___x_1337_;
v_a_1241_ = v___x_1343_;
goto v___jp_1228_;
}
else
{
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1344_; uint8_t v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1341_);
v___x_1345_ = lean_unbox(v_a_1344_);
lean_dec(v_a_1344_);
v___y_1229_ = v___y_1298_;
v___y_1230_ = v___y_1293_;
v___y_1231_ = v___y_1294_;
v___y_1232_ = v___y_1291_;
v___y_1233_ = v___y_1300_;
v___y_1234_ = v___y_1296_;
v___y_1235_ = v___y_1292_;
v___y_1236_ = v___y_1299_;
v___y_1237_ = v___y_1295_;
v___y_1238_ = v___y_1297_;
v___y_1239_ = v___y_1290_;
v___y_1240_ = v___x_1337_;
v_a_1241_ = v___x_1345_;
goto v___jp_1228_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_T_1184_);
lean_dec_ref(v_H_1183_);
lean_dec_ref(v_00_u03c3s_1182_);
lean_dec(v_goal_1180_);
v_a_1346_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1341_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___boxed(lean_object** _args){
lean_object* v_goal_1370_ = _args[0];
lean_object* v_ent_1371_ = _args[1];
lean_object* v_00_u03c3s_1372_ = _args[2];
lean_object* v_H_1373_ = _args[3];
lean_object* v_T_1374_ = _args[4];
lean_object* v_a_1375_ = _args[5];
lean_object* v_a_1376_ = _args[6];
lean_object* v_a_1377_ = _args[7];
lean_object* v_a_1378_ = _args[8];
lean_object* v_a_1379_ = _args[9];
lean_object* v_a_1380_ = _args[10];
lean_object* v_a_1381_ = _args[11];
lean_object* v_a_1382_ = _args[12];
lean_object* v_a_1383_ = _args[13];
lean_object* v_a_1384_ = _args[14];
lean_object* v_a_1385_ = _args[15];
lean_object* v_a_1386_ = _args[16];
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(v_goal_1370_, v_ent_1371_, v_00_u03c3s_1372_, v_H_1373_, v_T_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec_ref(v_ent_1371_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0(lean_object* v_mvarId_1388_, lean_object* v_val_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_mvarId_1388_, v_val_1389_, v___y_1398_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___boxed(lean_object* v_mvarId_1403_, lean_object* v_val_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0(v_mvarId_1403_, v_val_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(v_x_1419_, v_x_1420_, v_x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, size_t v_x_1425_, size_t v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1424_, v_x_1425_, v_x_1426_, v_x_1427_, v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
size_t v_x_29458__boxed_1436_; size_t v_x_29459__boxed_1437_; lean_object* v_res_1438_; 
v_x_29458__boxed_1436_ = lean_unbox_usize(v_x_1432_);
lean_dec(v_x_1432_);
v_x_29459__boxed_1437_ = lean_unbox_usize(v_x_1433_);
lean_dec(v_x_1433_);
v_res_1438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1(v_00_u03b2_1430_, v_x_1431_, v_x_29458__boxed_1436_, v_x_29459__boxed_1437_, v_x_1434_, v_x_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1439_, lean_object* v_n_1440_, lean_object* v_k_1441_, lean_object* v_v_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1440_, v_k_1441_, v_v_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1444_, size_t v_depth_1445_, lean_object* v_keys_1446_, lean_object* v_vals_1447_, lean_object* v_heq_1448_, lean_object* v_i_1449_, lean_object* v_entries_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1445_, v_keys_1446_, v_vals_1447_, v_i_1449_, v_entries_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_depth_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_heq_1456_, lean_object* v_i_1457_, lean_object* v_entries_1458_){
_start:
{
size_t v_depth_boxed_1459_; lean_object* v_res_1460_; 
v_depth_boxed_1459_ = lean_unbox_usize(v_depth_1453_);
lean_dec(v_depth_1453_);
v_res_1460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1452_, v_depth_boxed_1459_, v_keys_1454_, v_vals_1455_, v_heq_1456_, v_i_1457_, v_entries_1458_);
lean_dec_ref(v_vals_1455_);
lean_dec_ref(v_keys_1454_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1462_, v_x_1463_, v_x_1464_, v_x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(lean_object* v_args_1467_, lean_object* v_endIdx_1468_, lean_object* v_b_1469_, lean_object* v_i_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_nat_dec_le(v_endIdx_1468_, v_i_1470_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = l_Lean_instInhabitedExpr;
v___x_1480_ = lean_array_get_borrowed(v___x_1479_, v_args_1467_, v_i_1470_);
lean_inc(v___x_1480_);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_1469_, v___x_1480_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_nat_add(v_i_1470_, v___x_1483_);
lean_dec(v_i_1470_);
v_b_1469_ = v_a_1482_;
v_i_1470_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_i_1470_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_i_1470_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1469_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg___boxed(lean_object* v_args_1487_, lean_object* v_endIdx_1488_, lean_object* v_b_1489_, lean_object* v_i_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1487_, v_endIdx_1488_, v_b_1489_, v_i_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v_endIdx_1488_);
lean_dec_ref(v_args_1487_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(lean_object* v_f_1499_, lean_object* v_args_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_array_get_size(v_args_1500_);
v___x_1515_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1500_, v___x_1514_, v_f_1499_, v___x_1513_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1___boxed(lean_object* v_f_1516_, lean_object* v_args_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_f_1516_, v_args_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_args_1517_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_f_1531_, lean_object* v_a_u2081_1532_, lean_object* v_a_u2082_1533_, lean_object* v_a_u2083_1534_, lean_object* v_a_u2084_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_1531_, v_a_u2081_1532_, v_a_u2082_1533_, v_a_u2083_1534_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_1549_, v_a_u2084_1535_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1550_;
}
else
{
lean_dec_ref(v_a_u2084_1535_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_f_1551_ = _args[0];
lean_object* v_a_u2081_1552_ = _args[1];
lean_object* v_a_u2082_1553_ = _args[2];
lean_object* v_a_u2083_1554_ = _args[3];
lean_object* v_a_u2084_1555_ = _args[4];
lean_object* v___y_1556_ = _args[5];
lean_object* v___y_1557_ = _args[6];
lean_object* v___y_1558_ = _args[7];
lean_object* v___y_1559_ = _args[8];
lean_object* v___y_1560_ = _args[9];
lean_object* v___y_1561_ = _args[10];
lean_object* v___y_1562_ = _args[11];
lean_object* v___y_1563_ = _args[12];
lean_object* v___y_1564_ = _args[13];
lean_object* v___y_1565_ = _args[14];
lean_object* v___y_1566_ = _args[15];
lean_object* v___y_1567_ = _args[16];
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_1551_, v_a_u2081_1552_, v_a_u2082_1553_, v_a_u2083_1554_, v_a_u2084_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_1569_, lean_object* v_a_u2081_1570_, lean_object* v_a_u2082_1571_, lean_object* v_a_u2083_1572_, lean_object* v_a_u2084_1573_, lean_object* v_a_u2085_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_1569_, v_a_u2081_1570_, v_a_u2082_1571_, v_a_u2083_1572_, v_a_u2084_1573_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_1588_, v_a_u2085_1574_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1589_;
}
else
{
lean_dec_ref(v_a_u2085_1574_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object** _args){
lean_object* v_f_1590_ = _args[0];
lean_object* v_a_u2081_1591_ = _args[1];
lean_object* v_a_u2082_1592_ = _args[2];
lean_object* v_a_u2083_1593_ = _args[3];
lean_object* v_a_u2084_1594_ = _args[4];
lean_object* v_a_u2085_1595_ = _args[5];
lean_object* v___y_1596_ = _args[6];
lean_object* v___y_1597_ = _args[7];
lean_object* v___y_1598_ = _args[8];
lean_object* v___y_1599_ = _args[9];
lean_object* v___y_1600_ = _args[10];
lean_object* v___y_1601_ = _args[11];
lean_object* v___y_1602_ = _args[12];
lean_object* v___y_1603_ = _args[13];
lean_object* v___y_1604_ = _args[14];
lean_object* v___y_1605_ = _args[15];
lean_object* v___y_1606_ = _args[16];
lean_object* v___y_1607_ = _args[17];
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_1590_, v_a_u2081_1591_, v_a_u2082_1592_, v_a_u2083_1593_, v_a_u2084_1594_, v_a_u2085_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_1609_, lean_object* v_head_1610_, lean_object* v_H_1611_, lean_object* v_00_u03c3s_1612_, lean_object* v_ent_1613_, lean_object* v_args_1614_, lean_object* v_wpConst_1615_, lean_object* v_m_1616_, lean_object* v_ps_1617_, lean_object* v_instWP_1618_, lean_object* v_00_u03b1_1619_, lean_object* v_e_x27_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_1615_, v_m_1616_, v_ps_1617_, v_instWP_1618_, v_00_u03b1_1619_, v_e_x27_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(2u);
v___x_1636_ = lean_array_set(v_args_1614_, v___x_1635_, v_a_1634_);
v___x_1637_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_1610_, v___x_1636_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec_ref(v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_1613_, v_00_u03c3s_1612_, v_H_1611_, v_a_1638_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1609_, v_a_1640_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
return v___x_1641_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_goal_1609_);
v_a_1642_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1639_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1639_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_ent_1613_);
lean_dec_ref(v_00_u03c3s_1612_);
lean_dec_ref(v_H_1611_);
lean_dec(v_goal_1609_);
v_a_1650_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1637_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1637_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_args_1614_);
lean_dec_ref(v_ent_1613_);
lean_dec_ref(v_00_u03c3s_1612_);
lean_dec_ref(v_H_1611_);
lean_dec_ref(v_head_1610_);
lean_dec(v_goal_1609_);
v_a_1658_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1633_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1633_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object** _args){
lean_object* v_goal_1666_ = _args[0];
lean_object* v_head_1667_ = _args[1];
lean_object* v_H_1668_ = _args[2];
lean_object* v_00_u03c3s_1669_ = _args[3];
lean_object* v_ent_1670_ = _args[4];
lean_object* v_args_1671_ = _args[5];
lean_object* v_wpConst_1672_ = _args[6];
lean_object* v_m_1673_ = _args[7];
lean_object* v_ps_1674_ = _args[8];
lean_object* v_instWP_1675_ = _args[9];
lean_object* v_00_u03b1_1676_ = _args[10];
lean_object* v_e_x27_1677_ = _args[11];
lean_object* v_a_1678_ = _args[12];
lean_object* v_a_1679_ = _args[13];
lean_object* v_a_1680_ = _args[14];
lean_object* v_a_1681_ = _args[15];
lean_object* v_a_1682_ = _args[16];
lean_object* v_a_1683_ = _args[17];
lean_object* v_a_1684_ = _args[18];
lean_object* v_a_1685_ = _args[19];
lean_object* v_a_1686_ = _args[20];
lean_object* v_a_1687_ = _args[21];
lean_object* v_a_1688_ = _args[22];
lean_object* v_a_1689_ = _args[23];
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_1666_, v_head_1667_, v_H_1668_, v_00_u03c3s_1669_, v_ent_1670_, v_args_1671_, v_wpConst_1672_, v_m_1673_, v_ps_1674_, v_instWP_1675_, v_00_u03b1_1676_, v_e_x27_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(lean_object* v_args_1691_, lean_object* v_endIdx_1692_, lean_object* v_b_1693_, lean_object* v_i_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1691_, v_endIdx_1692_, v_b_1693_, v_i_1694_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___boxed(lean_object* v_args_1708_, lean_object* v_endIdx_1709_, lean_object* v_b_1710_, lean_object* v_i_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(v_args_1708_, v_endIdx_1709_, v_b_1710_, v_i_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v_endIdx_1709_);
lean_dec_ref(v_args_1708_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(lean_object* v_revArgs_1725_, lean_object* v_start_1726_, lean_object* v_b_1727_, lean_object* v_i_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_le(v_i_1728_, v_start_1726_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v_i_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1737_ = lean_unsigned_to_nat(1u);
v_i_1738_ = lean_nat_sub(v_i_1728_, v___x_1737_);
lean_dec(v_i_1728_);
v___x_1739_ = l_Lean_instInhabitedExpr;
v___x_1740_ = lean_array_get_borrowed(v___x_1739_, v_revArgs_1725_, v_i_1738_);
lean_inc(v___x_1740_);
v___x_1741_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_1727_, v___x_1740_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
v_b_1727_ = v_a_1742_;
v_i_1728_ = v_i_1738_;
goto _start;
}
else
{
lean_dec(v_i_1738_);
return v___x_1741_;
}
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_i_1728_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1727_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_1745_, lean_object* v_start_1746_, lean_object* v_b_1747_, lean_object* v_i_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1745_, v_start_1746_, v_b_1747_, v_i_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v_start_1746_);
lean_dec_ref(v_revArgs_1745_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(lean_object* v_f_1757_, lean_object* v_revArgs_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_revArgs_1758_);
v___x_1773_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1758_, v___x_1771_, v_f_1757_, v___x_1772_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0___boxed(lean_object* v_f_1774_, lean_object* v_revArgs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_f_1774_, v_revArgs_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_revArgs_1775_);
return v_res_1788_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(lean_object* v_goal_1792_, lean_object* v_head_1793_, lean_object* v_H_1794_, lean_object* v_00_u03c3s_1795_, lean_object* v_ent_1796_, lean_object* v_args_1797_, lean_object* v_wpConst_1798_, lean_object* v_m_1799_, lean_object* v_ps_1800_, lean_object* v_instWP_1801_, lean_object* v_00_u03b1_1802_, lean_object* v_e_1803_, lean_object* v_f_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
if (lean_obj_tag(v_f_1804_) == 8)
{
lean_object* v_declName_1817_; lean_object* v_type_1818_; lean_object* v_value_1819_; lean_object* v_body_1820_; uint8_t v_nondep_1821_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v_options_1901_; uint8_t v_hasTrace_1902_; 
v_declName_1817_ = lean_ctor_get(v_f_1804_, 0);
lean_inc(v_declName_1817_);
v_type_1818_ = lean_ctor_get(v_f_1804_, 1);
lean_inc_ref(v_type_1818_);
v_value_1819_ = lean_ctor_get(v_f_1804_, 2);
lean_inc_ref(v_value_1819_);
v_body_1820_ = lean_ctor_get(v_f_1804_, 3);
lean_inc_ref(v_body_1820_);
v_nondep_1821_ = lean_ctor_get_uint8(v_f_1804_, sizeof(void*)*4 + 8);
lean_dec_ref(v_f_1804_);
v_options_1901_ = lean_ctor_get(v_a_1814_, 2);
v_hasTrace_1902_ = lean_ctor_get_uint8(v_options_1901_, sizeof(void*)*1);
if (v_hasTrace_1902_ == 0)
{
v___y_1823_ = v_a_1805_;
v___y_1824_ = v_a_1806_;
v___y_1825_ = v_a_1807_;
v___y_1826_ = v_a_1808_;
v___y_1827_ = v_a_1809_;
v___y_1828_ = v_a_1810_;
v___y_1829_ = v_a_1811_;
v___y_1830_ = v_a_1812_;
v___y_1831_ = v_a_1813_;
v___y_1832_ = v_a_1814_;
v___y_1833_ = v_a_1815_;
goto v___jp_1822_;
}
else
{
lean_object* v_inheritedTraceOptions_1903_; lean_object* v_cls_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_inheritedTraceOptions_1903_ = lean_ctor_get(v_a_1814_, 13);
v_cls_1904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_1905_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1903_, v_options_1901_, v___x_1905_);
if (v___x_1906_ == 0)
{
v___y_1823_ = v_a_1805_;
v___y_1824_ = v_a_1806_;
v___y_1825_ = v_a_1807_;
v___y_1826_ = v_a_1808_;
v___y_1827_ = v_a_1809_;
v___y_1828_ = v_a_1810_;
v___y_1829_ = v_a_1811_;
v___y_1830_ = v_a_1812_;
v___y_1831_ = v_a_1813_;
v___y_1832_ = v_a_1814_;
v___y_1833_ = v_a_1815_;
goto v___jp_1822_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1);
lean_inc(v_declName_1817_);
v___x_1908_ = l_Lean_MessageData_ofName(v_declName_1817_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1904_, v___x_1909_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_dec_ref(v___x_1910_);
v___y_1823_ = v_a_1805_;
v___y_1824_ = v_a_1806_;
v___y_1825_ = v_a_1807_;
v___y_1826_ = v_a_1808_;
v___y_1827_ = v_a_1809_;
v___y_1828_ = v_a_1810_;
v___y_1829_ = v_a_1811_;
v___y_1830_ = v_a_1812_;
v___y_1831_ = v_a_1813_;
v___y_1832_ = v_a_1814_;
v___y_1833_ = v_a_1815_;
goto v___jp_1822_;
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_body_1820_);
lean_dec_ref(v_value_1819_);
lean_dec_ref(v_type_1818_);
lean_dec(v_declName_1817_);
lean_dec_ref(v_e_1803_);
lean_dec_ref(v_00_u03b1_1802_);
lean_dec_ref(v_instWP_1801_);
lean_dec_ref(v_ps_1800_);
lean_dec_ref(v_m_1799_);
lean_dec_ref(v_wpConst_1798_);
lean_dec_ref(v_args_1797_);
lean_dec_ref(v_ent_1796_);
lean_dec_ref(v_00_u03c3s_1795_);
lean_dec_ref(v_H_1794_);
lean_dec_ref(v_head_1793_);
lean_dec(v_goal_1792_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
v___jp_1822_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = l_Lean_Expr_getAppNumArgs(v_e_1803_);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
lean_dec(v___x_1834_);
v___x_1836_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1803_, v___x_1835_);
v___x_1837_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_body_1820_, v___x_1836_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v___x_1836_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_1798_, v_m_1799_, v_ps_1800_, v_instWP_1801_, v_00_u03b1_1802_, v_a_1838_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = lean_unsigned_to_nat(2u);
v___x_1842_ = lean_array_set(v_args_1797_, v___x_1841_, v_a_1840_);
v___x_1843_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_1793_, v___x_1842_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v___x_1842_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_1796_, v_00_u03c3s_1795_, v_H_1794_, v_a_1844_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_Expr_letE___override(v_declName_1817_, v_type_1818_, v_value_1819_, v_a_1846_, v_nondep_1821_);
v___x_1848_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1792_, v___x_1847_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1860_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1860_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1860_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1849_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1856_);
v___x_1858_ = v___x_1851_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1848_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1848_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_value_1819_);
lean_dec_ref(v_type_1818_);
lean_dec(v_declName_1817_);
lean_dec(v_goal_1792_);
v_a_1869_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1845_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1845_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_value_1819_);
lean_dec_ref(v_type_1818_);
lean_dec(v_declName_1817_);
lean_dec_ref(v_ent_1796_);
lean_dec_ref(v_00_u03c3s_1795_);
lean_dec_ref(v_H_1794_);
lean_dec(v_goal_1792_);
v_a_1877_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1843_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1843_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v_value_1819_);
lean_dec_ref(v_type_1818_);
lean_dec(v_declName_1817_);
lean_dec_ref(v_args_1797_);
lean_dec_ref(v_ent_1796_);
lean_dec_ref(v_00_u03c3s_1795_);
lean_dec_ref(v_H_1794_);
lean_dec_ref(v_head_1793_);
lean_dec(v_goal_1792_);
v_a_1885_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1839_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1839_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_value_1819_);
lean_dec_ref(v_type_1818_);
lean_dec(v_declName_1817_);
lean_dec_ref(v_00_u03b1_1802_);
lean_dec_ref(v_instWP_1801_);
lean_dec_ref(v_ps_1800_);
lean_dec_ref(v_m_1799_);
lean_dec_ref(v_wpConst_1798_);
lean_dec_ref(v_args_1797_);
lean_dec_ref(v_ent_1796_);
lean_dec_ref(v_00_u03c3s_1795_);
lean_dec_ref(v_H_1794_);
lean_dec_ref(v_head_1793_);
lean_dec(v_goal_1792_);
v_a_1893_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1837_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1837_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_f_1804_);
lean_dec_ref(v_e_1803_);
lean_dec_ref(v_00_u03b1_1802_);
lean_dec_ref(v_instWP_1801_);
lean_dec_ref(v_ps_1800_);
lean_dec_ref(v_m_1799_);
lean_dec_ref(v_wpConst_1798_);
lean_dec_ref(v_args_1797_);
lean_dec_ref(v_ent_1796_);
lean_dec_ref(v_00_u03c3s_1795_);
lean_dec_ref(v_H_1794_);
lean_dec_ref(v_head_1793_);
lean_dec(v_goal_1792_);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___boxed(lean_object** _args){
lean_object* v_goal_1921_ = _args[0];
lean_object* v_head_1922_ = _args[1];
lean_object* v_H_1923_ = _args[2];
lean_object* v_00_u03c3s_1924_ = _args[3];
lean_object* v_ent_1925_ = _args[4];
lean_object* v_args_1926_ = _args[5];
lean_object* v_wpConst_1927_ = _args[6];
lean_object* v_m_1928_ = _args[7];
lean_object* v_ps_1929_ = _args[8];
lean_object* v_instWP_1930_ = _args[9];
lean_object* v_00_u03b1_1931_ = _args[10];
lean_object* v_e_1932_ = _args[11];
lean_object* v_f_1933_ = _args[12];
lean_object* v_a_1934_ = _args[13];
lean_object* v_a_1935_ = _args[14];
lean_object* v_a_1936_ = _args[15];
lean_object* v_a_1937_ = _args[16];
lean_object* v_a_1938_ = _args[17];
lean_object* v_a_1939_ = _args[18];
lean_object* v_a_1940_ = _args[19];
lean_object* v_a_1941_ = _args[20];
lean_object* v_a_1942_ = _args[21];
lean_object* v_a_1943_ = _args[22];
lean_object* v_a_1944_ = _args[23];
lean_object* v_a_1945_ = _args[24];
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_1921_, v_head_1922_, v_H_1923_, v_00_u03c3s_1924_, v_ent_1925_, v_args_1926_, v_wpConst_1927_, v_m_1928_, v_ps_1929_, v_instWP_1930_, v_00_u03b1_1931_, v_e_1932_, v_f_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(lean_object* v_revArgs_1947_, lean_object* v_start_1948_, lean_object* v_b_1949_, lean_object* v_i_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1947_, v_start_1948_, v_b_1949_, v_i_1950_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___boxed(lean_object* v_revArgs_1964_, lean_object* v_start_1965_, lean_object* v_b_1966_, lean_object* v_i_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(v_revArgs_1964_, v_start_1965_, v_b_1966_, v_i_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_start_1965_);
lean_dec_ref(v_revArgs_1964_);
return v_res_1980_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0(void){
_start:
{
uint8_t v___x_1981_; uint64_t v___x_1982_; 
v___x_1981_ = 2;
v___x_1982_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(lean_object* v_goal_1989_, lean_object* v_head_1990_, lean_object* v_H_1991_, lean_object* v_00_u03c3s_1992_, lean_object* v_ent_1993_, lean_object* v_args_1994_, lean_object* v_wpConst_1995_, lean_object* v_m_1996_, lean_object* v_ps_1997_, lean_object* v_instWP_1998_, lean_object* v_00_u03b1_1999_, lean_object* v_e_2000_, lean_object* v_excessArgs_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; 
lean_inc_ref(v_e_2000_);
v___x_2014_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2000_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2166_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2166_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2166_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
if (lean_obj_tag(v_a_2015_) == 1)
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2161_; 
lean_del_object(v___x_2017_);
v_val_2019_ = lean_ctor_get(v_a_2015_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2021_ = v_a_2015_;
v_isShared_2022_ = v_isSharedCheck_2161_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v_a_2015_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2161_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; uint8_t v_foApprox_2024_; uint8_t v_ctxApprox_2025_; uint8_t v_quasiPatternApprox_2026_; uint8_t v_constApprox_2027_; uint8_t v_isDefEqStuckEx_2028_; uint8_t v_unificationHints_2029_; uint8_t v_proofIrrelevance_2030_; uint8_t v_assignSyntheticOpaque_2031_; uint8_t v_offsetCnstrs_2032_; uint8_t v_etaStruct_2033_; uint8_t v_univApprox_2034_; uint8_t v_iota_2035_; uint8_t v_beta_2036_; uint8_t v_proj_2037_; uint8_t v_zeta_2038_; uint8_t v_zetaDelta_2039_; uint8_t v_zetaUnused_2040_; uint8_t v_zetaHave_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2160_; 
v___x_2023_ = l_Lean_Meta_Context_config(v_a_2009_);
v_foApprox_2024_ = lean_ctor_get_uint8(v___x_2023_, 0);
v_ctxApprox_2025_ = lean_ctor_get_uint8(v___x_2023_, 1);
v_quasiPatternApprox_2026_ = lean_ctor_get_uint8(v___x_2023_, 2);
v_constApprox_2027_ = lean_ctor_get_uint8(v___x_2023_, 3);
v_isDefEqStuckEx_2028_ = lean_ctor_get_uint8(v___x_2023_, 4);
v_unificationHints_2029_ = lean_ctor_get_uint8(v___x_2023_, 5);
v_proofIrrelevance_2030_ = lean_ctor_get_uint8(v___x_2023_, 6);
v_assignSyntheticOpaque_2031_ = lean_ctor_get_uint8(v___x_2023_, 7);
v_offsetCnstrs_2032_ = lean_ctor_get_uint8(v___x_2023_, 8);
v_etaStruct_2033_ = lean_ctor_get_uint8(v___x_2023_, 10);
v_univApprox_2034_ = lean_ctor_get_uint8(v___x_2023_, 11);
v_iota_2035_ = lean_ctor_get_uint8(v___x_2023_, 12);
v_beta_2036_ = lean_ctor_get_uint8(v___x_2023_, 13);
v_proj_2037_ = lean_ctor_get_uint8(v___x_2023_, 14);
v_zeta_2038_ = lean_ctor_get_uint8(v___x_2023_, 15);
v_zetaDelta_2039_ = lean_ctor_get_uint8(v___x_2023_, 16);
v_zetaUnused_2040_ = lean_ctor_get_uint8(v___x_2023_, 17);
v_zetaHave_2041_ = lean_ctor_get_uint8(v___x_2023_, 18);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2043_ = v___x_2023_;
v_isShared_2044_ = v_isSharedCheck_2160_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v___x_2023_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2160_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
uint8_t v_trackZetaDelta_2045_; lean_object* v_zetaDeltaSet_2046_; lean_object* v_lctx_2047_; lean_object* v_localInstances_2048_; lean_object* v_defEqCtx_x3f_2049_; lean_object* v_synthPendingDepth_2050_; lean_object* v_canUnfold_x3f_2051_; uint8_t v_univApprox_2052_; uint8_t v_inTypeClassResolution_2053_; uint8_t v_cacheInferType_2054_; uint8_t v___x_2055_; lean_object* v_config_2057_; 
v_trackZetaDelta_2045_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*7);
v_zetaDeltaSet_2046_ = lean_ctor_get(v_a_2009_, 1);
v_lctx_2047_ = lean_ctor_get(v_a_2009_, 2);
v_localInstances_2048_ = lean_ctor_get(v_a_2009_, 3);
v_defEqCtx_x3f_2049_ = lean_ctor_get(v_a_2009_, 4);
v_synthPendingDepth_2050_ = lean_ctor_get(v_a_2009_, 5);
v_canUnfold_x3f_2051_ = lean_ctor_get(v_a_2009_, 6);
v_univApprox_2052_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2053_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*7 + 2);
v_cacheInferType_2054_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*7 + 3);
v___x_2055_ = 2;
if (v_isShared_2044_ == 0)
{
v_config_2057_ = v___x_2043_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 0, v_foApprox_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 1, v_ctxApprox_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 2, v_quasiPatternApprox_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 3, v_constApprox_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 4, v_isDefEqStuckEx_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 5, v_unificationHints_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 6, v_proofIrrelevance_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 7, v_assignSyntheticOpaque_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 8, v_offsetCnstrs_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 10, v_etaStruct_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 11, v_univApprox_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 12, v_iota_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 13, v_beta_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 14, v_proj_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 15, v_zeta_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 16, v_zetaDelta_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 17, v_zetaUnused_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, 18, v_zetaHave_2041_);
v_config_2057_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
uint64_t v___x_2058_; uint64_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v_key_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_ctor_set_uint8(v_config_2057_, 9, v___x_2055_);
v___x_2058_ = l_Lean_Meta_Context_configKey(v_a_2009_);
v___x_2059_ = 2ULL;
v___x_2060_ = lean_uint64_shift_right(v___x_2058_, v___x_2059_);
v___x_2061_ = lean_uint64_shift_left(v___x_2060_, v___x_2059_);
v___x_2062_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0);
v_key_2063_ = lean_uint64_lor(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2064_, 0, v_config_2057_);
lean_ctor_set_uint64(v___x_2064_, sizeof(void*)*1, v_key_2063_);
lean_inc(v_canUnfold_x3f_2051_);
lean_inc(v_synthPendingDepth_2050_);
lean_inc(v_defEqCtx_x3f_2049_);
lean_inc_ref(v_localInstances_2048_);
lean_inc_ref(v_lctx_2047_);
lean_inc(v_zetaDeltaSet_2046_);
v___x_2065_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v_zetaDeltaSet_2046_);
lean_ctor_set(v___x_2065_, 2, v_lctx_2047_);
lean_ctor_set(v___x_2065_, 3, v_localInstances_2048_);
lean_ctor_set(v___x_2065_, 4, v_defEqCtx_x3f_2049_);
lean_ctor_set(v___x_2065_, 5, v_synthPendingDepth_2050_);
lean_ctor_set(v___x_2065_, 6, v_canUnfold_x3f_2051_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*7, v_trackZetaDelta_2045_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*7 + 1, v_univApprox_2052_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2053_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*7 + 3, v_cacheInferType_2054_);
v___x_2066_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_2000_, v___x_2065_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_2066_);
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2105_; 
lean_del_object(v___x_2021_);
lean_dec(v_val_2019_);
lean_dec_ref(v_excessArgs_2001_);
lean_dec_ref(v_e_2000_);
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2070_ = v_a_2067_;
v_isShared_2071_ = v_isSharedCheck_2105_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v_a_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2105_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2068_, v_a_2008_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_1989_, v_head_1990_, v_H_1991_, v_00_u03c3s_1992_, v_ent_1993_, v_args_1994_, v_wpConst_1995_, v_m_1996_, v_ps_1997_, v_instWP_1998_, v_00_u03b1_1999_, v_a_2073_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2088_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2088_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_a_2075_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2081_);
v___x_2083_ = v___x_2070_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2083_);
v___x_2085_ = v___x_2077_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_del_object(v___x_2070_);
v_a_2089_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2074_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2074_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_2070_);
lean_dec_ref(v_00_u03b1_1999_);
lean_dec_ref(v_instWP_1998_);
lean_dec_ref(v_ps_1997_);
lean_dec_ref(v_m_1996_);
lean_dec_ref(v_wpConst_1995_);
lean_dec_ref(v_args_1994_);
lean_dec_ref(v_ent_1993_);
lean_dec_ref(v_00_u03c3s_1992_);
lean_dec_ref(v_H_1991_);
lean_dec_ref(v_head_1990_);
lean_dec(v_goal_1989_);
v_a_2097_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2072_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2072_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v___x_2106_; 
lean_dec(v_a_2067_);
lean_dec_ref(v_00_u03b1_1999_);
lean_dec_ref(v_wpConst_1995_);
lean_dec_ref(v_args_1994_);
lean_dec_ref(v_ent_1993_);
lean_dec_ref(v_H_1991_);
lean_dec_ref(v_head_1990_);
v___x_2106_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_val_2019_, v_m_1996_, v_00_u03c3s_1992_, v_ps_1997_, v_instWP_1998_, v_excessArgs_2001_, v_a_2003_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2);
v___x_2109_ = l_Lean_indentExpr(v_e_2000_);
lean_inc_ref(v___x_2109_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2110_);
v___x_2112_ = v___x_2021_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2107_, v_goal_1989_, v___x_2112_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2133_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2133_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2133_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
if (lean_obj_tag(v_a_2114_) == 1)
{
lean_object* v_mvarIds_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v___x_2109_);
v_mvarIds_2118_ = lean_ctor_get(v_a_2114_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_a_2114_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2120_ = v_a_2114_;
v_isShared_2121_ = v_isSharedCheck_2129_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_mvarIds_2118_);
lean_dec(v_a_2114_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2129_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 4);
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_mvarIds_2118_);
v___x_2123_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2124_);
v___x_2126_ = v___x_2116_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_del_object(v___x_2116_);
lean_dec(v_a_2114_);
v___x_2130_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2109_);
v___x_2132_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_2131_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
return v___x_2132_;
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___x_2109_);
v_a_2134_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2113_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2113_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_del_object(v___x_2021_);
lean_dec_ref(v_e_2000_);
lean_dec(v_goal_1989_);
v_a_2143_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2106_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2106_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2021_);
lean_dec(v_val_2019_);
lean_dec_ref(v_excessArgs_2001_);
lean_dec_ref(v_e_2000_);
lean_dec_ref(v_00_u03b1_1999_);
lean_dec_ref(v_instWP_1998_);
lean_dec_ref(v_ps_1997_);
lean_dec_ref(v_m_1996_);
lean_dec_ref(v_wpConst_1995_);
lean_dec_ref(v_args_1994_);
lean_dec_ref(v_ent_1993_);
lean_dec_ref(v_00_u03c3s_1992_);
lean_dec_ref(v_H_1991_);
lean_dec_ref(v_head_1990_);
lean_dec(v_goal_1989_);
v_a_2151_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2066_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2066_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_a_2015_);
lean_dec_ref(v_excessArgs_2001_);
lean_dec_ref(v_e_2000_);
lean_dec_ref(v_00_u03b1_1999_);
lean_dec_ref(v_instWP_1998_);
lean_dec_ref(v_ps_1997_);
lean_dec_ref(v_m_1996_);
lean_dec_ref(v_wpConst_1995_);
lean_dec_ref(v_args_1994_);
lean_dec_ref(v_ent_1993_);
lean_dec_ref(v_00_u03c3s_1992_);
lean_dec_ref(v_H_1991_);
lean_dec_ref(v_head_1990_);
lean_dec(v_goal_1989_);
v___x_2162_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2162_);
v___x_2164_ = v___x_2017_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v_excessArgs_2001_);
lean_dec_ref(v_e_2000_);
lean_dec_ref(v_00_u03b1_1999_);
lean_dec_ref(v_instWP_1998_);
lean_dec_ref(v_ps_1997_);
lean_dec_ref(v_m_1996_);
lean_dec_ref(v_wpConst_1995_);
lean_dec_ref(v_args_1994_);
lean_dec_ref(v_ent_1993_);
lean_dec_ref(v_00_u03c3s_1992_);
lean_dec_ref(v_H_1991_);
lean_dec_ref(v_head_1990_);
lean_dec(v_goal_1989_);
v_a_2167_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2014_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2014_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___boxed(lean_object** _args){
lean_object* v_goal_2175_ = _args[0];
lean_object* v_head_2176_ = _args[1];
lean_object* v_H_2177_ = _args[2];
lean_object* v_00_u03c3s_2178_ = _args[3];
lean_object* v_ent_2179_ = _args[4];
lean_object* v_args_2180_ = _args[5];
lean_object* v_wpConst_2181_ = _args[6];
lean_object* v_m_2182_ = _args[7];
lean_object* v_ps_2183_ = _args[8];
lean_object* v_instWP_2184_ = _args[9];
lean_object* v_00_u03b1_2185_ = _args[10];
lean_object* v_e_2186_ = _args[11];
lean_object* v_excessArgs_2187_ = _args[12];
lean_object* v_a_2188_ = _args[13];
lean_object* v_a_2189_ = _args[14];
lean_object* v_a_2190_ = _args[15];
lean_object* v_a_2191_ = _args[16];
lean_object* v_a_2192_ = _args[17];
lean_object* v_a_2193_ = _args[18];
lean_object* v_a_2194_ = _args[19];
lean_object* v_a_2195_ = _args[20];
lean_object* v_a_2196_ = _args[21];
lean_object* v_a_2197_ = _args[22];
lean_object* v_a_2198_ = _args[23];
lean_object* v_a_2199_ = _args[24];
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_2175_, v_head_2176_, v_H_2177_, v_00_u03c3s_2178_, v_ent_2179_, v_args_2180_, v_wpConst_2181_, v_m_2182_, v_ps_2183_, v_instWP_2184_, v_00_u03b1_2185_, v_e_2186_, v_excessArgs_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
return v_res_2200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(lean_object* v_goal_2204_, lean_object* v_head_2205_, lean_object* v_H_2206_, lean_object* v_00_u03c3s_2207_, lean_object* v_ent_2208_, lean_object* v_args_2209_, lean_object* v_wpConst_2210_, lean_object* v_m_2211_, lean_object* v_ps_2212_, lean_object* v_instWP_2213_, lean_object* v_00_u03b1_2214_, lean_object* v_e_2215_, lean_object* v_f_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_Expr_fvarId_x3f(v_f_2216_);
if (lean_obj_tag(v___x_2229_) == 1)
{
lean_object* v_val_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2337_; 
v_val_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2337_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_val_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2337_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = 0;
lean_inc(v_val_2230_);
v___x_2235_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_2230_, v___x_2234_, v_a_2224_, v_a_2226_, v_a_2227_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2328_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2328_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2328_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2323_; 
lean_del_object(v___x_2238_);
v_val_2240_ = lean_ctor_get(v_a_2236_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_a_2236_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2242_ = v_a_2236_;
v_isShared_2243_ = v_isSharedCheck_2323_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_val_2240_);
lean_dec(v_a_2236_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2323_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v_options_2295_; uint8_t v_hasTrace_2296_; 
v_options_2295_ = lean_ctor_get(v_a_2226_, 2);
v_hasTrace_2296_ = lean_ctor_get_uint8(v_options_2295_, sizeof(void*)*1);
if (v_hasTrace_2296_ == 0)
{
lean_dec(v_val_2230_);
v___y_2245_ = v_a_2217_;
v___y_2246_ = v_a_2218_;
v___y_2247_ = v_a_2219_;
v___y_2248_ = v_a_2220_;
v___y_2249_ = v_a_2221_;
v___y_2250_ = v_a_2222_;
v___y_2251_ = v_a_2223_;
v___y_2252_ = v_a_2224_;
v___y_2253_ = v_a_2225_;
v___y_2254_ = v_a_2226_;
v___y_2255_ = v_a_2227_;
goto v___jp_2244_;
}
else
{
lean_object* v_inheritedTraceOptions_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_inheritedTraceOptions_2297_ = lean_ctor_get(v_a_2226_, 13);
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_2299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_2300_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2297_, v_options_2295_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v_val_2230_);
v___y_2245_ = v_a_2217_;
v___y_2246_ = v_a_2218_;
v___y_2247_ = v_a_2219_;
v___y_2248_ = v_a_2220_;
v___y_2249_ = v_a_2221_;
v___y_2250_ = v_a_2222_;
v___y_2251_ = v_a_2223_;
v___y_2252_ = v_a_2224_;
v___y_2253_ = v_a_2225_;
v___y_2254_ = v_a_2226_;
v___y_2255_ = v_a_2227_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_FVarId_getUserName___redArg(v_val_2230_, v_a_2224_, v_a_2226_, v_a_2227_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1);
v___x_2304_ = l_Lean_MessageData_ofName(v_a_2302_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_2298_, v___x_2305_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_dec_ref(v___x_2306_);
v___y_2245_ = v_a_2217_;
v___y_2246_ = v_a_2218_;
v___y_2247_ = v_a_2219_;
v___y_2248_ = v_a_2220_;
v___y_2249_ = v_a_2221_;
v___y_2250_ = v_a_2222_;
v___y_2251_ = v_a_2223_;
v___y_2252_ = v_a_2224_;
v___y_2253_ = v_a_2225_;
v___y_2254_ = v_a_2226_;
v___y_2255_ = v_a_2227_;
goto v___jp_2244_;
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_del_object(v___x_2242_);
lean_dec(v_val_2240_);
lean_del_object(v___x_2232_);
lean_dec_ref(v_e_2215_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2242_);
lean_dec(v_val_2240_);
lean_del_object(v___x_2232_);
lean_dec_ref(v_e_2215_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v_a_2315_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2301_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2301_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
v___jp_2244_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2256_ = l_Lean_Expr_getAppNumArgs(v_e_2215_);
v___x_2257_ = lean_mk_empty_array_with_capacity(v___x_2256_);
lean_dec(v___x_2256_);
v___x_2258_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_2215_, v___x_2257_);
v___x_2259_ = l_Lean_Expr_betaRev(v_val_2240_, v___x_2258_, v___x_2234_, v___x_2234_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_2259_, v___y_2251_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2204_, v_head_2205_, v_H_2206_, v_00_u03c3s_2207_, v_ent_2208_, v_args_2209_, v_wpConst_2210_, v_m_2211_, v_ps_2212_, v_instWP_2213_, v_00_u03b1_2214_, v_a_2261_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2278_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2278_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2278_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_a_2263_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 4);
lean_ctor_set(v___x_2232_, 0, v___x_2268_);
v___x_2270_ = v___x_2232_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2270_);
v___x_2272_ = v___x_2242_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2272_);
v___x_2274_ = v___x_2265_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_del_object(v___x_2242_);
lean_del_object(v___x_2232_);
v_a_2279_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2262_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2262_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_del_object(v___x_2242_);
lean_del_object(v___x_2232_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v_a_2287_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2260_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2260_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
lean_dec(v_a_2236_);
lean_del_object(v___x_2232_);
lean_dec(v_val_2230_);
lean_dec_ref(v_e_2215_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v___x_2324_ = lean_box(0);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2324_);
v___x_2326_ = v___x_2238_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
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
lean_del_object(v___x_2232_);
lean_dec(v_val_2230_);
lean_dec_ref(v_e_2215_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v_a_2329_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2235_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2235_);
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
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v___x_2229_);
lean_dec_ref(v_e_2215_);
lean_dec_ref(v_00_u03b1_2214_);
lean_dec_ref(v_instWP_2213_);
lean_dec_ref(v_ps_2212_);
lean_dec_ref(v_m_2211_);
lean_dec_ref(v_wpConst_2210_);
lean_dec_ref(v_args_2209_);
lean_dec_ref(v_ent_2208_);
lean_dec_ref(v_00_u03c3s_2207_);
lean_dec_ref(v_H_2206_);
lean_dec_ref(v_head_2205_);
lean_dec(v_goal_2204_);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___boxed(lean_object** _args){
lean_object* v_goal_2340_ = _args[0];
lean_object* v_head_2341_ = _args[1];
lean_object* v_H_2342_ = _args[2];
lean_object* v_00_u03c3s_2343_ = _args[3];
lean_object* v_ent_2344_ = _args[4];
lean_object* v_args_2345_ = _args[5];
lean_object* v_wpConst_2346_ = _args[6];
lean_object* v_m_2347_ = _args[7];
lean_object* v_ps_2348_ = _args[8];
lean_object* v_instWP_2349_ = _args[9];
lean_object* v_00_u03b1_2350_ = _args[10];
lean_object* v_e_2351_ = _args[11];
lean_object* v_f_2352_ = _args[12];
lean_object* v_a_2353_ = _args[13];
lean_object* v_a_2354_ = _args[14];
lean_object* v_a_2355_ = _args[15];
lean_object* v_a_2356_ = _args[16];
lean_object* v_a_2357_ = _args[17];
lean_object* v_a_2358_ = _args[18];
lean_object* v_a_2359_ = _args[19];
lean_object* v_a_2360_ = _args[20];
lean_object* v_a_2361_ = _args[21];
lean_object* v_a_2362_ = _args[22];
lean_object* v_a_2363_ = _args[23];
lean_object* v_a_2364_ = _args[24];
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_2340_, v_head_2341_, v_H_2342_, v_00_u03c3s_2343_, v_ent_2344_, v_args_2345_, v_wpConst_2346_, v_m_2347_, v_ps_2348_, v_instWP_2349_, v_00_u03b1_2350_, v_e_2351_, v_f_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec_ref(v_f_2352_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(lean_object* v_cls_2366_, lean_object* v_____do__lift_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_options_2380_; uint8_t v_hasTrace_2381_; 
v_options_2380_ = lean_ctor_get(v___y_2377_, 2);
v_hasTrace_2381_ = lean_ctor_get_uint8(v_options_2380_, sizeof(void*)*1);
if (v_hasTrace_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_cls_2366_);
v___x_2382_ = lean_box(v_hasTrace_2381_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
v___x_2385_ = l_Lean_Name_append(v___x_2384_, v_cls_2366_);
v___x_2386_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2367_, v_options_2380_, v___x_2385_);
lean_dec(v___x_2385_);
v___x_2387_ = lean_box(v___x_2386_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(lean_object* v_cls_2389_, lean_object* v_____do__lift_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_2389_, v_____do__lift_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_____do__lift_2390_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
if (lean_obj_tag(v_a_2404_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = l_List_reverse___redArg(v_a_2405_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2417_; 
v_head_2407_ = lean_ctor_get(v_a_2404_, 0);
v_tail_2408_ = lean_ctor_get(v_a_2404_, 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2410_ = v_a_2404_;
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_tail_2408_);
lean_inc(v_head_2407_);
lean_dec(v_a_2404_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_MessageData_ofExpr(v_head_2407_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v_a_2405_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_a_2405_);
v___x_2414_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
v_a_2404_ = v_tail_2408_;
v_a_2405_ = v___x_2414_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_2432_ = l_Lean_stringToMessageData(v___x_2431_);
return v___x_2432_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_2444_ = l_Lean_stringToMessageData(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_2447_ = l_Lean_stringToMessageData(v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_2450_ = l_Lean_stringToMessageData(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_goal_2459_, lean_object* v_e_2460_, lean_object* v_excessArgs_2461_, lean_object* v_m_2462_, lean_object* v_00_u03c3s_2463_, lean_object* v_ps_2464_, lean_object* v_instWP_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2540_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2732_; lean_object* v_f_2758_; uint8_t v___x_2759_; 
v_f_2758_ = l_Lean_Expr_getAppFn(v_e_2460_);
v___x_2759_ = l_Lean_Expr_isConst(v_f_2758_);
if (v___x_2759_ == 0)
{
uint8_t v___x_2760_; 
v___x_2760_ = l_Lean_Expr_isFVar(v_f_2758_);
lean_dec_ref(v_f_2758_);
v___y_2732_ = v___x_2760_;
goto v___jp_2731_;
}
else
{
lean_dec_ref(v_f_2758_);
v___y_2732_ = v___x_2759_;
goto v___jp_2731_;
}
v___jp_2478_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_e_2460_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
v___jp_2481_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_2495_ = l_Lean_indentExpr(v_e_2460_);
lean_inc_ref(v___x_2495_);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_inc_ref(v___y_2482_);
v___x_2498_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_2482_, v_goal_2459_, v___x_2497_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2530_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2530_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2530_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
if (lean_obj_tag(v_a_2499_) == 1)
{
lean_object* v_mvarIds_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___y_2482_);
v_mvarIds_2503_ = lean_ctor_get(v_a_2499_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_a_2499_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2505_ = v_a_2499_;
v_isShared_2506_ = v_isSharedCheck_2513_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_mvarIds_2503_);
lean_dec(v_a_2499_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2513_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 4);
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_mvarIds_2503_);
v___x_2508_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2508_);
v___x_2510_ = v___x_2501_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_expr_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_del_object(v___x_2501_);
lean_dec(v_a_2499_);
v_expr_2514_ = lean_ctor_get(v___y_2482_, 0);
lean_inc_ref(v_expr_2514_);
lean_dec_ref(v___y_2482_);
v___x_2515_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_2516_ = l_Lean_MessageData_ofExpr(v_expr_2514_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2495_);
v___x_2521_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_2520_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v___x_2495_);
lean_dec_ref(v___y_2482_);
v_a_2531_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2498_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2498_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___y_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
v___jp_2545_:
{
lean_object* v___x_2560_; 
lean_inc(v_goal_2459_);
lean_inc_ref(v___y_2548_);
v___x_2560_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(v___y_2548_, v_goal_2459_, v_excessArgs_2461_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
if (lean_obj_tag(v_a_2561_) == 1)
{
lean_object* v_options_2562_; uint8_t v_hasTrace_2563_; 
lean_dec_ref(v___y_2548_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_options_2562_ = lean_ctor_get(v___y_2558_, 2);
v_hasTrace_2563_ = lean_ctor_get_uint8(v_options_2562_, sizeof(void*)*1);
if (v_hasTrace_2563_ == 0)
{
lean_object* v_val_2564_; 
lean_dec(v___y_2546_);
v_val_2564_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_val_2564_);
lean_dec_ref(v_a_2561_);
v___y_2540_ = v_val_2564_;
goto v___jp_2539_;
}
else
{
lean_object* v_val_2565_; lean_object* v_inheritedTraceOptions_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_val_2565_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_val_2565_);
lean_dec_ref(v_a_2561_);
v_inheritedTraceOptions_2566_ = lean_ctor_get(v___y_2558_, 13);
v___x_2567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
lean_inc(v___y_2546_);
v___x_2568_ = l_Lean_Name_append(v___x_2567_, v___y_2546_);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2566_, v_options_2562_, v___x_2568_);
lean_dec(v___x_2568_);
if (v___x_2569_ == 0)
{
lean_dec(v___y_2546_);
v___y_2540_ = v_val_2565_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_2571_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2546_, v___x_2570_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_dec_ref(v___x_2571_);
v___y_2540_ = v_val_2565_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_val_2565_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
else
{
lean_object* v___x_2580_; 
lean_dec(v_a_2561_);
v___x_2580_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v___y_2548_, v_m_2462_, v_00_u03c3s_2463_, v_ps_2464_, v_instWP_2465_, v_excessArgs_2461_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v_inheritedTraceOptions_2582_; lean_object* v___x_2583_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v_inheritedTraceOptions_2582_ = lean_ctor_get(v___y_2558_, 13);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2549_);
lean_inc_ref(v_inheritedTraceOptions_2582_);
v___x_2583_ = lean_apply_13(v___y_2547_, v_inheritedTraceOptions_2582_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, lean_box(0));
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = lean_unbox(v_a_2584_);
lean_dec(v_a_2584_);
if (v___x_2585_ == 0)
{
lean_dec(v___y_2546_);
v___y_2482_ = v_a_2581_;
v___y_2483_ = v___y_2549_;
v___y_2484_ = v___y_2550_;
v___y_2485_ = v___y_2551_;
v___y_2486_ = v___y_2552_;
v___y_2487_ = v___y_2553_;
v___y_2488_ = v___y_2554_;
v___y_2489_ = v___y_2555_;
v___y_2490_ = v___y_2556_;
v___y_2491_ = v___y_2557_;
v___y_2492_ = v___y_2558_;
v___y_2493_ = v___y_2559_;
goto v___jp_2481_;
}
else
{
lean_object* v_expr_2586_; lean_object* v___x_2587_; 
v_expr_2586_ = lean_ctor_get(v_a_2581_, 0);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc_ref(v_expr_2586_);
v___x_2587_ = lean_infer_type(v_expr_2586_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref(v___x_2587_);
v___x_2589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_2590_ = l_Lean_MessageData_ofExpr(v_a_2588_);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2546_, v___x_2591_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref(v___x_2592_);
v___y_2482_ = v_a_2581_;
v___y_2483_ = v___y_2549_;
v___y_2484_ = v___y_2550_;
v___y_2485_ = v___y_2551_;
v___y_2486_ = v___y_2552_;
v___y_2487_ = v___y_2553_;
v___y_2488_ = v___y_2554_;
v___y_2489_ = v___y_2555_;
v___y_2490_ = v___y_2556_;
v___y_2491_ = v___y_2557_;
v___y_2492_ = v___y_2558_;
v___y_2493_ = v___y_2559_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_a_2581_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_a_2581_);
lean_dec(v___y_2546_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2601_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2587_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2587_);
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
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2581_);
lean_dec(v___y_2546_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2609_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2583_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2583_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___y_2546_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2617_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2580_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2580_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2546_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2625_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2560_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2560_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
v___jp_2633_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___y_2638_);
lean_ctor_set(v___x_2650_, 1, v___y_2649_);
lean_inc(v___y_2641_);
v___x_2651_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2641_, v___x_2650_, v___y_2639_, v___y_2642_, v___y_2635_, v___y_2640_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_dec_ref(v___x_2651_);
v___y_2546_ = v___y_2641_;
v___y_2547_ = v___y_2637_;
v___y_2548_ = v___y_2645_;
v___y_2549_ = v___y_2647_;
v___y_2550_ = v___y_2643_;
v___y_2551_ = v___y_2634_;
v___y_2552_ = v___y_2648_;
v___y_2553_ = v___y_2636_;
v___y_2554_ = v___y_2644_;
v___y_2555_ = v___y_2646_;
v___y_2556_ = v___y_2639_;
v___y_2557_ = v___y_2642_;
v___y_2558_ = v___y_2635_;
v___y_2559_ = v___y_2640_;
goto v___jp_2545_;
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2641_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
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
v___jp_2660_:
{
lean_object* v_specThms_2674_; lean_object* v___x_2675_; 
v_specThms_2674_ = lean_ctor_get(v___y_2663_, 0);
lean_inc_ref(v_e_2460_);
v___x_2675_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_specThms_2674_, v_e_2460_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2722_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2722_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2722_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
if (lean_obj_tag(v_a_2676_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
lean_dec(v___y_2661_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec(v_goal_2459_);
v_a_2680_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v_a_2676_);
v___x_2681_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2681_, 0, v_e_2460_);
lean_ctor_set(v___x_2681_, 1, v_m_2462_);
lean_ctor_set(v___x_2681_, 2, v_a_2680_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
else
{
lean_object* v_a_2685_; lean_object* v_inheritedTraceOptions_2686_; lean_object* v___x_2687_; 
lean_del_object(v___x_2678_);
v_a_2685_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v_a_2676_);
v_inheritedTraceOptions_2686_ = lean_ctor_get(v___y_2672_, 13);
lean_inc_ref(v___y_2662_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v___y_2667_);
lean_inc_ref(v___y_2666_);
lean_inc(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc_ref(v_inheritedTraceOptions_2686_);
v___x_2687_ = lean_apply_13(v___y_2662_, v_inheritedTraceOptions_2686_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, lean_box(0));
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; uint8_t v___x_2689_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref(v___x_2687_);
v___x_2689_ = lean_unbox(v_a_2688_);
lean_dec(v_a_2688_);
if (v___x_2689_ == 0)
{
v___y_2546_ = v___y_2661_;
v___y_2547_ = v___y_2662_;
v___y_2548_ = v_a_2685_;
v___y_2549_ = v___y_2663_;
v___y_2550_ = v___y_2664_;
v___y_2551_ = v___y_2665_;
v___y_2552_ = v___y_2666_;
v___y_2553_ = v___y_2667_;
v___y_2554_ = v___y_2668_;
v___y_2555_ = v___y_2669_;
v___y_2556_ = v___y_2670_;
v___y_2557_ = v___y_2671_;
v___y_2558_ = v___y_2672_;
v___y_2559_ = v___y_2673_;
goto v___jp_2545_;
}
else
{
lean_object* v_proof_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_proof_2690_ = lean_ctor_get(v_a_2685_, 1);
v___x_2691_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
lean_inc_ref(v_e_2460_);
v___x_2692_ = l_Lean_MessageData_ofExpr(v_e_2460_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
switch(lean_obj_tag(v_proof_2690_))
{
case 0:
{
lean_object* v_declName_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_declName_2696_ = lean_ctor_get(v_proof_2690_, 0);
v___x_2697_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
lean_inc(v_declName_2696_);
v___x_2698_ = l_Lean_MessageData_ofName(v_declName_2696_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___y_2634_ = v___y_2665_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2667_;
v___y_2637_ = v___y_2662_;
v___y_2638_ = v___x_2695_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2673_;
v___y_2641_ = v___y_2661_;
v___y_2642_ = v___y_2671_;
v___y_2643_ = v___y_2664_;
v___y_2644_ = v___y_2668_;
v___y_2645_ = v_a_2685_;
v___y_2646_ = v___y_2669_;
v___y_2647_ = v___y_2663_;
v___y_2648_ = v___y_2666_;
v___y_2649_ = v___x_2699_;
goto v___jp_2633_;
}
case 1:
{
lean_object* v_fvarId_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_fvarId_2700_ = lean_ctor_get(v_proof_2690_, 0);
v___x_2701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
lean_inc(v_fvarId_2700_);
v___x_2702_ = l_Lean_mkFVar(v_fvarId_2700_);
v___x_2703_ = l_Lean_MessageData_ofExpr(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___y_2634_ = v___y_2665_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2667_;
v___y_2637_ = v___y_2662_;
v___y_2638_ = v___x_2695_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2673_;
v___y_2641_ = v___y_2661_;
v___y_2642_ = v___y_2671_;
v___y_2643_ = v___y_2664_;
v___y_2644_ = v___y_2668_;
v___y_2645_ = v_a_2685_;
v___y_2646_ = v___y_2669_;
v___y_2647_ = v___y_2663_;
v___y_2648_ = v___y_2666_;
v___y_2649_ = v___x_2704_;
goto v___jp_2633_;
}
default: 
{
lean_object* v_ref_2705_; lean_object* v_proof_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_ref_2705_ = lean_ctor_get(v_proof_2690_, 1);
v_proof_2706_ = lean_ctor_get(v_proof_2690_, 2);
v___x_2707_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
lean_inc(v_ref_2705_);
v___x_2708_ = l_Lean_MessageData_ofSyntax(v_ref_2705_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
lean_inc_ref(v_proof_2706_);
v___x_2712_ = l_Lean_MessageData_ofExpr(v_proof_2706_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___y_2634_ = v___y_2665_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2667_;
v___y_2637_ = v___y_2662_;
v___y_2638_ = v___x_2695_;
v___y_2639_ = v___y_2670_;
v___y_2640_ = v___y_2673_;
v___y_2641_ = v___y_2661_;
v___y_2642_ = v___y_2671_;
v___y_2643_ = v___y_2664_;
v___y_2644_ = v___y_2668_;
v___y_2645_ = v_a_2685_;
v___y_2646_ = v___y_2669_;
v___y_2647_ = v___y_2663_;
v___y_2648_ = v___y_2666_;
v___y_2649_ = v___x_2713_;
goto v___jp_2633_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2685_);
lean_dec(v___y_2661_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2714_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2687_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2687_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v___y_2661_);
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2723_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2675_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2675_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
v___jp_2731_:
{
if (v___y_2732_ == 0)
{
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec(v_goal_2459_);
goto v___jp_2478_;
}
else
{
lean_object* v_inheritedTraceOptions_2733_; lean_object* v_cls_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_inheritedTraceOptions_2733_ = lean_ctor_get(v_a_2475_, 13);
v_cls_2734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___f_2735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22));
v___x_2736_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_2734_, v_inheritedTraceOptions_2733_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = lean_unbox(v_a_2737_);
lean_dec(v_a_2737_);
if (v___x_2738_ == 0)
{
v___y_2661_ = v_cls_2734_;
v___y_2662_ = v___f_2735_;
v___y_2663_ = v_a_2466_;
v___y_2664_ = v_a_2467_;
v___y_2665_ = v_a_2468_;
v___y_2666_ = v_a_2469_;
v___y_2667_ = v_a_2470_;
v___y_2668_ = v_a_2471_;
v___y_2669_ = v_a_2472_;
v___y_2670_ = v_a_2473_;
v___y_2671_ = v_a_2474_;
v___y_2672_ = v_a_2475_;
v___y_2673_ = v_a_2476_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2739_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24);
lean_inc_ref(v_e_2460_);
v___x_2740_ = l_Lean_MessageData_ofExpr(v_e_2460_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
lean_inc_ref(v_excessArgs_2461_);
v___x_2744_ = lean_array_to_list(v_excessArgs_2461_);
v___x_2745_ = lean_box(0);
v___x_2746_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_2744_, v___x_2745_);
v___x_2747_ = l_Lean_MessageData_ofList(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2743_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_2734_, v___x_2748_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_dec_ref(v___x_2749_);
v___y_2661_ = v_cls_2734_;
v___y_2662_ = v___f_2735_;
v___y_2663_ = v_a_2466_;
v___y_2664_ = v_a_2467_;
v___y_2665_ = v_a_2468_;
v___y_2666_ = v_a_2469_;
v___y_2667_ = v_a_2470_;
v___y_2668_ = v_a_2471_;
v___y_2669_ = v_a_2472_;
v___y_2670_ = v_a_2473_;
v___y_2671_ = v_a_2474_;
v___y_2672_ = v_a_2475_;
v___y_2673_ = v_a_2476_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec_ref(v_instWP_2465_);
lean_dec_ref(v_ps_2464_);
lean_dec_ref(v_00_u03c3s_2463_);
lean_dec_ref(v_m_2462_);
lean_dec_ref(v_excessArgs_2461_);
lean_dec_ref(v_e_2460_);
lean_dec(v_goal_2459_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object** _args){
lean_object* v_goal_2761_ = _args[0];
lean_object* v_e_2762_ = _args[1];
lean_object* v_excessArgs_2763_ = _args[2];
lean_object* v_m_2764_ = _args[3];
lean_object* v_00_u03c3s_2765_ = _args[4];
lean_object* v_ps_2766_ = _args[5];
lean_object* v_instWP_2767_ = _args[6];
lean_object* v_a_2768_ = _args[7];
lean_object* v_a_2769_ = _args[8];
lean_object* v_a_2770_ = _args[9];
lean_object* v_a_2771_ = _args[10];
lean_object* v_a_2772_ = _args[11];
lean_object* v_a_2773_ = _args[12];
lean_object* v_a_2774_ = _args[13];
lean_object* v_a_2775_ = _args[14];
lean_object* v_a_2776_ = _args[15];
lean_object* v_a_2777_ = _args[16];
lean_object* v_a_2778_ = _args[17];
lean_object* v_a_2779_ = _args[18];
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_goal_2761_, v_e_2762_, v_excessArgs_2763_, v_m_2764_, v_00_u03c3s_2765_, v_ps_2766_, v_instWP_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(lean_object* v_x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
lean_inc(v___y_2788_);
lean_inc_ref(v___y_2787_);
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
v___x_2794_ = lean_apply_12(v_x_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, lean_box(0));
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed(lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(v_x_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(lean_object* v_mvarId_2809_, lean_object* v_x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; 
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc(v___y_2813_);
lean_inc(v___y_2812_);
lean_inc_ref(v___y_2811_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2823_, 0, v_x_2810_);
lean_closure_set(v___f_2823_, 1, v___y_2811_);
lean_closure_set(v___f_2823_, 2, v___y_2812_);
lean_closure_set(v___f_2823_, 3, v___y_2813_);
lean_closure_set(v___f_2823_, 4, v___y_2814_);
lean_closure_set(v___f_2823_, 5, v___y_2815_);
lean_closure_set(v___f_2823_, 6, v___y_2816_);
lean_closure_set(v___f_2823_, 7, v___y_2817_);
v___x_2824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2809_, v___f_2823_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2824_) == 0)
{
return v___x_2824_;
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___boxed(lean_object* v_mvarId_2833_, lean_object* v_x_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_2833_, v_x_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(lean_object* v_00_u03b1_2848_, lean_object* v_mvarId_2849_, lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_2849_, v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___boxed(lean_object* v_00_u03b1_2864_, lean_object* v_mvarId_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(v_00_u03b1_2864_, v_mvarId_2865_, v_x_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 5)
{
lean_object* v_fn_2883_; lean_object* v_arg_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_fn_2883_ = lean_ctor_get(v_x_2880_, 0);
lean_inc_ref(v_fn_2883_);
v_arg_2884_ = lean_ctor_get(v_x_2880_, 1);
lean_inc_ref(v_arg_2884_);
lean_dec_ref(v_x_2880_);
v___x_2885_ = lean_array_set(v_x_2881_, v_x_2882_, v_arg_2884_);
v___x_2886_ = lean_unsigned_to_nat(1u);
v___x_2887_ = lean_nat_sub(v_x_2882_, v___x_2886_);
lean_dec(v_x_2882_);
v_x_2880_ = v_fn_2883_;
v_x_2881_ = v___x_2885_;
v_x_2882_ = v___x_2887_;
goto _start;
}
else
{
lean_object* v___x_2889_; 
lean_dec(v_x_2882_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_x_2880_);
lean_ctor_set(v___x_2889_, 1, v_x_2881_);
return v___x_2889_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v_dummy_2896_; 
v___x_2895_ = lean_box(0);
v_dummy_2896_ = l_Lean_Expr_sort___override(v___x_2895_);
return v_dummy_2896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
v___x_2913_ = l_Lean_stringToMessageData(v___x_2912_);
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10));
v___x_2916_ = l_Lean_stringToMessageData(v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_r_2931_; lean_object* v___y_2932_; lean_object* v___y_2951_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___x_3022_; 
lean_inc(v_goal_2917_);
v___x_3022_ = l_Lean_MVarId_getType(v_goal_2917_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3248_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3248_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3248_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_options_3032_; lean_object* v_inheritedTraceOptions_3033_; uint8_t v_hasTrace_3034_; lean_object* v_cls_3035_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; 
v_options_3032_ = lean_ctor_get(v___y_2927_, 2);
v_inheritedTraceOptions_3033_ = lean_ctor_get(v___y_2927_, 13);
v_hasTrace_3034_ = lean_ctor_get_uint8(v_options_3032_, sizeof(void*)*1);
v_cls_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
if (v_hasTrace_3034_ == 0)
{
v___y_3037_ = v___y_2918_;
v___y_3038_ = v___y_2919_;
v___y_3039_ = v___y_2920_;
v___y_3040_ = v___y_2921_;
v___y_3041_ = v___y_2922_;
v___y_3042_ = v___y_2923_;
v___y_3043_ = v___y_2924_;
v___y_3044_ = v___y_2925_;
v___y_3045_ = v___y_2926_;
v___y_3046_ = v___y_2927_;
v___y_3047_ = v___y_2928_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3234_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3033_, v_options_3032_, v___x_3234_);
if (v___x_3235_ == 0)
{
v___y_3037_ = v___y_2918_;
v___y_3038_ = v___y_2919_;
v___y_3039_ = v___y_2920_;
v___y_3040_ = v___y_2921_;
v___y_3041_ = v___y_2922_;
v___y_3042_ = v___y_2923_;
v___y_3043_ = v___y_2924_;
v___y_3044_ = v___y_2925_;
v___y_3045_ = v___y_2926_;
v___y_3046_ = v___y_2927_;
v___y_3047_ = v___y_2928_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3236_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11);
lean_inc(v_a_3023_);
v___x_3237_ = l_Lean_MessageData_ofExpr(v_a_3023_);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3035_, v___x_3238_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref(v___x_3239_);
v___y_3037_ = v___y_2918_;
v___y_3038_ = v___y_2919_;
v___y_3039_ = v___y_2920_;
v___y_3040_ = v___y_2921_;
v___y_3041_ = v___y_2922_;
v___y_3042_ = v___y_2923_;
v___y_3043_ = v___y_2924_;
v___y_3044_ = v___y_2925_;
v___y_3045_ = v___y_2926_;
v___y_3046_ = v___y_2927_;
v___y_3047_ = v___y_2928_;
goto v___jp_3036_;
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
v___jp_3027_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_a_3023_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3028_);
v___x_3030_ = v___x_3025_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
v___jp_3036_:
{
lean_object* v___x_3048_; 
lean_inc(v_goal_2917_);
v___x_3048_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_2917_, v_a_3023_, v___y_3037_, v___y_3038_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3225_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3225_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3225_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
if (lean_obj_tag(v_a_3049_) == 1)
{
lean_object* v_val_3053_; lean_object* v___x_3055_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_val_3053_ = lean_ctor_get(v_a_3049_, 0);
lean_inc(v_val_3053_);
lean_dec_ref(v_a_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_val_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
else
{
lean_object* v___x_3057_; 
lean_del_object(v___x_3051_);
lean_dec(v_a_3049_);
lean_inc(v_goal_2917_);
v___x_3057_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_2917_, v_a_3023_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3216_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3216_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3216_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_a_3058_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3064_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_val_3062_ = lean_ctor_get(v_a_3058_, 0);
lean_inc(v_val_3062_);
lean_dec_ref(v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_val_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_val_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
else
{
lean_object* v___x_3066_; 
lean_del_object(v___x_3060_);
lean_dec(v_a_3058_);
lean_inc(v_goal_2917_);
v___x_3066_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_2917_, v_a_3023_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3207_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3207_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3207_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
if (lean_obj_tag(v_a_3067_) == 1)
{
lean_object* v_val_3071_; lean_object* v___x_3073_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_val_3071_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_val_3071_);
lean_dec_ref(v_a_3067_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_val_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_val_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
else
{
lean_object* v___x_3075_; 
lean_del_object(v___x_3069_);
lean_dec(v_a_3067_);
lean_inc(v_goal_2917_);
v___x_3075_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(v_goal_2917_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3198_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3198_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3198_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
if (lean_obj_tag(v_a_3076_) == 1)
{
lean_object* v_val_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3090_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_val_3080_ = lean_ctor_get(v_a_3076_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_a_3076_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3082_ = v_a_3076_;
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_val_3080_);
lean_dec(v_a_3076_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 4);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_val_3080_);
v___x_3085_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3087_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3085_);
v___x_3087_ = v___x_3078_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v___x_3091_; uint8_t v___x_3092_; 
lean_del_object(v___x_3078_);
lean_dec(v_a_3076_);
lean_inc(v_a_3023_);
v___x_3091_ = l_Lean_Expr_cleanupAnnotations(v_a_3023_);
v___x_3092_ = l_Lean_Expr_isApp(v___x_3091_);
if (v___x_3092_ == 0)
{
lean_dec_ref(v___x_3091_);
lean_dec(v_goal_2917_);
goto v___jp_3027_;
}
else
{
lean_object* v_arg_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_arg_3093_ = lean_ctor_get(v___x_3091_, 1);
lean_inc_ref(v_arg_3093_);
v___x_3094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3091_);
v___x_3095_ = l_Lean_Expr_isApp(v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec_ref(v___x_3094_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
goto v___jp_3027_;
}
else
{
lean_object* v_arg_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_arg_3096_ = lean_ctor_get(v___x_3094_, 1);
lean_inc_ref(v_arg_3096_);
v___x_3097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3094_);
v___x_3098_ = l_Lean_Expr_isApp(v___x_3097_);
if (v___x_3098_ == 0)
{
lean_dec_ref(v___x_3097_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
goto v___jp_3027_;
}
else
{
lean_object* v_arg_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v_arg_3099_ = lean_ctor_get(v___x_3097_, 1);
lean_inc_ref(v_arg_3099_);
v___x_3100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3097_);
v___x_3101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_3102_ = l_Lean_Expr_isConstOf(v___x_3100_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3103_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_inc(v_goal_2917_);
v___x_3103_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_2917_, v_arg_3093_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3189_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3189_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3189_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
if (lean_obj_tag(v_a_3104_) == 1)
{
lean_object* v_val_3108_; lean_object* v___x_3110_; 
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
v_val_3108_ = lean_ctor_get(v_a_3104_, 0);
lean_inc(v_val_3108_);
lean_dec_ref(v_a_3104_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_val_3108_);
v___x_3110_ = v___x_3106_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_val_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
else
{
lean_object* v___x_3112_; 
lean_del_object(v___x_3106_);
lean_dec(v_a_3104_);
lean_inc_ref(v_arg_3093_);
lean_inc_ref(v_arg_3096_);
lean_inc_ref(v_arg_3099_);
lean_inc_ref(v___x_3100_);
lean_inc(v_goal_2917_);
v___x_3112_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_2917_, v___x_3100_, v_arg_3099_, v_arg_3096_, v_arg_3093_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3180_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3180_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3180_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
if (lean_obj_tag(v_a_3113_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3119_; 
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
v_val_3117_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_val_3117_);
lean_dec_ref(v_a_3113_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_val_3117_);
v___x_3119_ = v___x_3115_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_val_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
else
{
lean_object* v_dummy_3121_; lean_object* v_nargs_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_fst_3127_; lean_object* v_snd_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3179_; 
lean_del_object(v___x_3115_);
lean_dec(v_a_3113_);
v_dummy_3121_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v_nargs_3122_ = l_Lean_Expr_getAppNumArgs(v_arg_3093_);
lean_inc(v_nargs_3122_);
v___x_3123_ = lean_mk_array(v_nargs_3122_, v_dummy_3121_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_sub(v_nargs_3122_, v___x_3124_);
lean_dec(v_nargs_3122_);
lean_inc_ref(v_arg_3093_);
v___x_3126_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(v_arg_3093_, v___x_3123_, v___x_3125_);
v_fst_3127_ = lean_ctor_get(v___x_3126_, 0);
v_snd_3128_ = lean_ctor_get(v___x_3126_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3130_ = v___x_3126_;
v_isShared_3131_ = v_isSharedCheck_3179_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_snd_3128_);
lean_inc(v_fst_3127_);
lean_dec(v___x_3126_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3179_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_3133_ = l_Lean_Expr_isConstOf(v_fst_3127_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
v___x_3134_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(v_goal_2917_, v___x_3100_, v_arg_3099_, v_arg_3096_, v_arg_3093_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec_ref(v___x_3100_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3135_ = l_Lean_instInhabitedExpr;
v___x_3136_ = lean_unsigned_to_nat(2u);
v___x_3137_ = lean_array_get_borrowed(v___x_3135_, v_snd_3128_, v___x_3136_);
lean_inc(v___x_3137_);
v___x_3138_ = l_Lean_Expr_cleanupAnnotations(v___x_3137_);
v___x_3139_ = l_Lean_Expr_isApp(v___x_3138_);
if (v___x_3139_ == 0)
{
lean_dec_ref(v___x_3138_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_arg_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_arg_3140_ = lean_ctor_get(v___x_3138_, 1);
lean_inc_ref(v_arg_3140_);
v___x_3141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3138_);
v___x_3142_ = l_Lean_Expr_isApp(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v___x_3141_);
lean_dec_ref(v_arg_3140_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_arg_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v_arg_3143_ = lean_ctor_get(v___x_3141_, 1);
lean_inc_ref(v_arg_3143_);
v___x_3144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3141_);
v___x_3145_ = l_Lean_Expr_isApp(v___x_3144_);
if (v___x_3145_ == 0)
{
lean_dec_ref(v___x_3144_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3140_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_arg_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_arg_3146_ = lean_ctor_get(v___x_3144_, 1);
lean_inc_ref(v_arg_3146_);
v___x_3147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3144_);
v___x_3148_ = l_Lean_Expr_isApp(v___x_3147_);
if (v___x_3148_ == 0)
{
lean_dec_ref(v___x_3147_);
lean_dec_ref(v_arg_3146_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3140_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_arg_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_arg_3149_ = lean_ctor_get(v___x_3147_, 1);
lean_inc_ref(v_arg_3149_);
v___x_3150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3147_);
v___x_3151_ = l_Lean_Expr_isApp(v___x_3150_);
if (v___x_3151_ == 0)
{
lean_dec_ref(v___x_3150_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_arg_3146_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3140_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_arg_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_arg_3152_ = lean_ctor_get(v___x_3150_, 1);
lean_inc_ref(v_arg_3152_);
v___x_3153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3150_);
v___x_3154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7));
v___x_3155_ = l_Lean_Expr_isConstOf(v___x_3153_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_arg_3152_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_arg_3146_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3140_);
lean_del_object(v___x_3130_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v___y_2951_ = v_arg_3093_;
goto v___jp_2950_;
}
else
{
lean_object* v_options_3156_; lean_object* v_inheritedTraceOptions_3157_; uint8_t v_hasTrace_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec_ref(v_arg_3093_);
v_options_3156_ = lean_ctor_get(v___y_3046_, 2);
v_inheritedTraceOptions_3157_ = lean_ctor_get(v___y_3046_, 13);
v_hasTrace_3158_ = lean_ctor_get_uint8(v_options_3156_, sizeof(void*)*1);
v___x_3159_ = lean_unsigned_to_nat(4u);
v___x_3160_ = lean_array_get_size(v_snd_3128_);
v___x_3161_ = l_Array_extract___redArg(v_snd_3128_, v___x_3159_, v___x_3160_);
v___x_3162_ = l_Lean_Expr_getAppFn(v_arg_3140_);
if (v_hasTrace_3158_ == 0)
{
lean_del_object(v___x_3130_);
v___y_2955_ = v___x_3153_;
v___y_2956_ = v_arg_3099_;
v___y_2957_ = v___x_3161_;
v___y_2958_ = v_arg_3143_;
v___y_2959_ = v_snd_3128_;
v___y_2960_ = v___x_3162_;
v___y_2961_ = v_fst_3127_;
v___y_2962_ = v___x_3100_;
v___y_2963_ = v_arg_3146_;
v___y_2964_ = v_arg_3152_;
v___y_2965_ = v_arg_3149_;
v___y_2966_ = v_arg_3140_;
v___y_2967_ = v_arg_3096_;
v___y_2968_ = v___y_3037_;
v___y_2969_ = v___y_3038_;
v___y_2970_ = v___y_3039_;
v___y_2971_ = v___y_3040_;
v___y_2972_ = v___y_3041_;
v___y_2973_ = v___y_3042_;
v___y_2974_ = v___y_3043_;
v___y_2975_ = v___y_3044_;
v___y_2976_ = v___y_3045_;
v___y_2977_ = v___y_3046_;
v___y_2978_ = v___y_3047_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_3164_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3157_, v_options_3156_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_del_object(v___x_3130_);
v___y_2955_ = v___x_3153_;
v___y_2956_ = v_arg_3099_;
v___y_2957_ = v___x_3161_;
v___y_2958_ = v_arg_3143_;
v___y_2959_ = v_snd_3128_;
v___y_2960_ = v___x_3162_;
v___y_2961_ = v_fst_3127_;
v___y_2962_ = v___x_3100_;
v___y_2963_ = v_arg_3146_;
v___y_2964_ = v_arg_3152_;
v___y_2965_ = v_arg_3149_;
v___y_2966_ = v_arg_3140_;
v___y_2967_ = v_arg_3096_;
v___y_2968_ = v___y_3037_;
v___y_2969_ = v___y_3038_;
v___y_2970_ = v___y_3039_;
v___y_2971_ = v___y_3040_;
v___y_2972_ = v___y_3041_;
v___y_2973_ = v___y_3042_;
v___y_2974_ = v___y_3043_;
v___y_2975_ = v___y_3044_;
v___y_2976_ = v___y_3045_;
v___y_2977_ = v___y_3046_;
v___y_2978_ = v___y_3047_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3165_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9);
lean_inc_ref(v_arg_3140_);
v___x_3166_ = l_Lean_MessageData_ofExpr(v_arg_3140_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 7);
lean_ctor_set(v___x_3130_, 1, v___x_3166_);
lean_ctor_set(v___x_3130_, 0, v___x_3165_);
v___x_3168_ = v___x_3130_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3035_, v___x_3168_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref(v___x_3169_);
v___y_2955_ = v___x_3153_;
v___y_2956_ = v_arg_3099_;
v___y_2957_ = v___x_3161_;
v___y_2958_ = v_arg_3143_;
v___y_2959_ = v_snd_3128_;
v___y_2960_ = v___x_3162_;
v___y_2961_ = v_fst_3127_;
v___y_2962_ = v___x_3100_;
v___y_2963_ = v_arg_3146_;
v___y_2964_ = v_arg_3152_;
v___y_2965_ = v_arg_3149_;
v___y_2966_ = v_arg_3140_;
v___y_2967_ = v_arg_3096_;
v___y_2968_ = v___y_3037_;
v___y_2969_ = v___y_3038_;
v___y_2970_ = v___y_3039_;
v___y_2971_ = v___y_3040_;
v___y_2972_ = v___y_3041_;
v___y_2973_ = v___y_3042_;
v___y_2974_ = v___y_3043_;
v___y_2975_ = v___y_3044_;
v___y_2976_ = v___y_3045_;
v___y_2977_ = v___y_3046_;
v___y_2978_ = v___y_3047_;
goto v___jp_2954_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v___x_3162_);
lean_dec_ref(v___x_3161_);
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_arg_3152_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_arg_3146_);
lean_dec_ref(v_arg_3143_);
lean_dec_ref(v_arg_3140_);
lean_dec(v_snd_3128_);
lean_dec(v_fst_3127_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec(v_goal_2917_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
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
}
}
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
v_a_3181_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3112_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3112_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_arg_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_arg_3093_);
lean_dec(v_goal_2917_);
v_a_3190_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3103_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3103_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
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
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_a_3199_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3075_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3075_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_a_3208_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3066_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3066_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_a_3217_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3057_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3057_);
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
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_goal_2917_);
v_a_3226_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3048_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3048_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_goal_2917_);
v_a_3249_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3022_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3022_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
v___jp_2930_:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_2932_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2933_, 0);
lean_dec(v_unused_2941_);
v___x_2935_ = v___x_2933_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v___x_2933_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v_r_2931_);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_r_2931_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v_r_2931_);
v_a_2942_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2933_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2933_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
v___jp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___y_2951_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
v___jp_2954_:
{
lean_object* v___x_2979_; 
lean_inc_ref(v___y_2960_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2955_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___y_2962_);
lean_inc_ref(v___y_2956_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___y_2961_);
lean_inc(v_goal_2917_);
v___x_2979_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_2917_, v___y_2961_, v___y_2967_, v___y_2956_, v___y_2962_, v___y_2959_, v___y_2955_, v___y_2964_, v___y_2965_, v___y_2963_, v___y_2958_, v___y_2966_, v___y_2960_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
if (lean_obj_tag(v_a_2980_) == 1)
{
lean_object* v_val_2981_; 
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v_goal_2917_);
v_val_2981_ = lean_ctor_get(v_a_2980_, 0);
lean_inc(v_val_2981_);
lean_dec_ref(v_a_2980_);
v_r_2931_ = v_val_2981_;
v___y_2932_ = v___y_2969_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2982_; 
lean_dec(v_a_2980_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2955_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___y_2962_);
lean_inc_ref(v___y_2956_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___y_2961_);
lean_inc(v_goal_2917_);
v___x_2982_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_2917_, v___y_2961_, v___y_2967_, v___y_2956_, v___y_2962_, v___y_2959_, v___y_2955_, v___y_2964_, v___y_2965_, v___y_2963_, v___y_2958_, v___y_2966_, v___y_2957_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
if (lean_obj_tag(v_a_2983_) == 1)
{
lean_object* v_val_2984_; 
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v_goal_2917_);
v_val_2984_ = lean_ctor_get(v_a_2983_, 0);
lean_inc(v_val_2984_);
lean_dec_ref(v_a_2983_);
v_r_2931_ = v_val_2984_;
v___y_2932_ = v___y_2969_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2985_; 
lean_dec(v_a_2983_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2956_);
lean_inc(v_goal_2917_);
v___x_2985_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_2917_, v___y_2961_, v___y_2967_, v___y_2956_, v___y_2962_, v___y_2959_, v___y_2955_, v___y_2964_, v___y_2965_, v___y_2963_, v___y_2958_, v___y_2966_, v___y_2960_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec_ref(v___y_2960_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
if (lean_obj_tag(v_a_2986_) == 1)
{
lean_object* v_val_2987_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2917_);
v_val_2987_ = lean_ctor_get(v_a_2986_, 0);
lean_inc(v_val_2987_);
lean_dec_ref(v_a_2986_);
v_r_2931_ = v_val_2987_;
v___y_2932_ = v___y_2969_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2988_; 
lean_dec(v_a_2986_);
v___x_2988_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_2969_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v___x_2988_);
v___x_2989_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_goal_2917_, v___y_2966_, v___y_2957_, v___y_2964_, v___y_2956_, v___y_2965_, v___y_2963_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
return v___x_2989_;
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2917_);
v_a_2990_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2988_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2988_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2917_);
v_a_2998_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2985_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2985_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v_goal_2917_);
v_a_3006_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2982_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2982_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v_goal_2917_);
v_a_3014_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2979_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2979_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_goal_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___f_3284_; lean_object* v___x_3285_; 
lean_inc(v_goal_3271_);
v___f_3284_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3284_, 0, v_goal_3271_);
v___x_3285_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_goal_3271_, v___f_3284_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_goal_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_goal_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
return v_res_3299_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
}
#ifdef __cplusplus
}
#endif
