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
lean_dec_ref_known(v_t_9_, 3);
v___x_14_ = lean_apply_3(v_k_10_, v_e_11_, v_monad_12_, v_thms_13_);
return v___x_14_;
}
case 4:
{
lean_object* v_subgoals_15_; lean_object* v___x_16_; 
v_subgoals_15_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_subgoals_15_);
lean_dec_ref_known(v_t_9_, 1);
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
lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_251_; 
v_ref_205_ = lean_ctor_get(v___y_202_, 5);
v___x_206_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_251_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_251_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_251_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v_traceState_212_; lean_object* v_env_213_; lean_object* v_nextMacroScope_214_; lean_object* v_ngen_215_; lean_object* v_auxDeclNGen_216_; lean_object* v_cache_217_; lean_object* v_messages_218_; lean_object* v_infoState_219_; lean_object* v_snapshotTasks_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_250_; 
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
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_250_ == 0)
{
v___x_222_ = v___x_211_;
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
else
{
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
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_250_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint64_t v_tid_224_; lean_object* v_traces_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_249_; 
v_tid_224_ = lean_ctor_get_uint64(v_traceState_212_, sizeof(void*)*1);
v_traces_225_ = lean_ctor_get(v_traceState_212_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_traceState_212_);
if (v_isSharedCheck_249_ == 0)
{
v___x_227_ = v_traceState_212_;
v_isShared_228_ = v_isSharedCheck_249_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_traces_225_);
lean_dec(v_traceState_212_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_249_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; double v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_229_ = lean_box(0);
v___x_230_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__0);
v___x_231_ = 0;
v___x_232_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__1));
v___x_233_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_233_, 0, v_cls_198_);
lean_ctor_set(v___x_233_, 1, v___x_229_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
lean_ctor_set_float(v___x_233_, sizeof(void*)*3, v___x_230_);
lean_ctor_set_float(v___x_233_, sizeof(void*)*3 + 8, v___x_230_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3 + 16, v___x_231_);
v___x_234_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___closed__2));
v___x_235_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v_a_207_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
lean_inc(v_ref_205_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_ref_205_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_PersistentArray_push___redArg(v_traces_225_, v___x_236_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_237_);
v___x_239_ = v___x_227_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_237_);
lean_ctor_set_uint64(v_reuseFailAlloc_248_, sizeof(void*)*1, v_tid_224_);
v___x_239_ = v_reuseFailAlloc_248_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 4, v___x_239_);
v___x_241_ = v___x_222_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_env_213_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_nextMacroScope_214_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_ngen_215_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v_auxDeclNGen_216_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_247_, 5, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_247_, 6, v_messages_218_);
lean_ctor_set(v_reuseFailAlloc_247_, 7, v_infoState_219_);
lean_ctor_set(v_reuseFailAlloc_247_, 8, v_snapshotTasks_220_);
v___x_241_ = v_reuseFailAlloc_247_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_st_ref_set(v___y_203_, v___x_241_);
v___x_243_ = lean_box(0);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_243_);
v___x_245_ = v___x_209_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg___boxed(lean_object* v_cls_252_, lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_252_, v_msg_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_ref_266_; lean_object* v___x_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_ref_266_ = lean_ctor_get(v___y_263_, 5);
v___x_267_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0_spec__0(v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_inc(v_ref_266_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_ref_266_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg___boxed(lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__0));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
v___x_301_ = l_Lean_Name_append(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__10));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__12));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__14));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(lean_object* v_goal_311_, lean_object* v_target_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; uint8_t v___x_453_; 
v___x_453_ = l_Lean_Expr_isLet(v_target_312_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_goal_311_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
else
{
uint8_t v_useJP_456_; 
v_useJP_456_ = lean_ctor_get_uint8(v_a_313_, sizeof(void*)*20 + 1);
if (v_useJP_456_ == 0)
{
v___y_402_ = v_a_313_;
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
goto v___jp_401_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = l_Lean_Expr_letName_x21(v_target_312_);
lean_inc(v___x_457_);
v___x_458_ = l_Lean_Elab_Tactic_Do_isJP(v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v___x_457_);
v___y_402_ = v_a_313_;
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
goto v___jp_401_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = l_Lean_Expr_letValue_x21(v_target_312_);
v___x_460_ = l_Lean_Expr_isLambda(v___x_459_);
lean_dec_ref(v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v___x_457_);
v___y_402_ = v_a_313_;
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
goto v___jp_401_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_goal_311_);
v___x_461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__13);
v___x_462_ = l_Lean_MessageData_ofName(v___x_457_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__15);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_465_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
v___jp_325_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
v___x_335_ = l_Lean_Expr_letName_x21(v_target_312_);
v___x_336_ = l_Lean_MessageData_ofName(v___x_335_);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_goal_311_, v___x_337_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_350_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_350_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_350_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_350_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v_a_339_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_346_);
v___x_348_ = v___x_341_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_338_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_338_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
v___jp_359_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = l_Lean_Expr_letBody_x21(v_target_312_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
v___x_369_ = lean_array_push(v___x_368_, v___y_360_);
v___x_370_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v___x_366_, v___x_369_, v___y_361_);
lean_dec_ref(v___x_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_311_, v_a_371_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_a_373_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_380_);
v___x_382_ = v___x_375_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_372_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_372_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_goal_311_);
v_a_393_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_370_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_370_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
v___jp_401_:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = l_Lean_Expr_letValue_x21(v_target_312_);
v___x_414_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v_options_415_; uint8_t v_hasTrace_416_; 
lean_dec_ref(v___x_413_);
v_options_415_ = lean_ctor_get(v___y_411_, 2);
v_hasTrace_416_ = lean_ctor_get_uint8(v_options_415_, sizeof(void*)*1);
if (v_hasTrace_416_ == 0)
{
v___y_326_ = v___y_402_;
v___y_327_ = v___y_403_;
v___y_328_ = v___y_407_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
goto v___jp_325_;
}
else
{
lean_object* v_inheritedTraceOptions_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_inheritedTraceOptions_417_ = lean_ctor_get(v___y_411_, 13);
v___x_418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_419_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_420_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_417_, v_options_415_, v___x_419_);
if (v___x_420_ == 0)
{
v___y_326_ = v___y_402_;
v___y_327_ = v___y_403_;
v___y_328_ = v___y_407_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
goto v___jp_325_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__1);
v___x_422_ = l_Lean_Expr_letName_x21(v_target_312_);
v___x_423_ = l_Lean_MessageData_ofName(v___x_422_);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_418_, v___x_424_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_dec_ref_known(v___x_425_, 1);
v___y_326_ = v___y_402_;
v___y_327_ = v___y_403_;
v___y_328_ = v___y_407_;
v___y_329_ = v___y_408_;
v___y_330_ = v___y_409_;
v___y_331_ = v___y_410_;
v___y_332_ = v___y_411_;
v___y_333_ = v___y_412_;
goto v___jp_325_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_goal_311_);
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
else
{
lean_object* v_options_434_; uint8_t v_hasTrace_435_; 
v_options_434_ = lean_ctor_get(v___y_411_, 2);
v_hasTrace_435_ = lean_ctor_get_uint8(v_options_434_, sizeof(void*)*1);
if (v_hasTrace_435_ == 0)
{
v___y_360_ = v___x_413_;
v___y_361_ = v___y_408_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
goto v___jp_359_;
}
else
{
lean_object* v_inheritedTraceOptions_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_inheritedTraceOptions_436_ = lean_ctor_get(v___y_411_, 13);
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_436_, v_options_434_, v___x_438_);
if (v___x_439_ == 0)
{
v___y_360_ = v___x_413_;
v___y_361_ = v___y_408_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
goto v___jp_359_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_440_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__11);
v___x_441_ = l_Lean_Expr_letName_x21(v_target_312_);
v___x_442_ = l_Lean_MessageData_ofName(v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_440_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_437_, v___x_443_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec_ref_known(v___x_444_, 1);
v___y_360_ = v___x_413_;
v___y_361_ = v___y_408_;
v___y_362_ = v___y_409_;
v___y_363_ = v___y_410_;
v___y_364_ = v___y_411_;
v___y_365_ = v___y_412_;
goto v___jp_359_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_413_);
lean_dec(v_goal_311_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___boxed(lean_object* v_goal_475_, lean_object* v_target_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_475_, v_target_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec_ref(v_target_476_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(lean_object* v_cls_490_, lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_490_, v_msg_491_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___boxed(lean_object* v_cls_505_, lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0(v_cls_505_, v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(lean_object* v_00_u03b1_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v_msg_521_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___boxed(lean_object* v_00_u03b1_535_, lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1(v_00_u03b1_535_, v_msg_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(lean_object* v_goal_556_, lean_object* v_target_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Expr_getAppFn(v_target_557_);
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___closed__2));
v___x_572_ = l_Lean_Expr_isConstOf(v___x_570_, v___x_571_);
lean_dec_ref(v___x_570_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_goal_556_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(v_goal_556_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_587_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_587_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_587_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v_a_576_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_583_);
v___x_585_ = v___x_578_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_575_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_575_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold___boxed(lean_object* v_goal_596_, lean_object* v_target_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_596_, v_target_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_target_597_);
return v_res_610_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__0));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5(void){
_start:
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = 0;
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__4));
v___x_623_ = l_Lean_MessageData_ofConstName(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__5);
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__1);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__7));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__8);
v___x_631_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__6);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
return v___x_632_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__10));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(lean_object* v_goal_636_, lean_object* v_T_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Expr_isLambda(v_T_637_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_goal_636_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v_entailsConsIntroRule_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_entailsConsIntroRule_653_ = lean_ctor_get(v_a_638_, 1);
v___x_654_ = lean_box(0);
lean_inc(v_goal_636_);
lean_inc_ref(v_entailsConsIntroRule_653_);
v___x_655_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsConsIntroRule_653_, v_goal_636_, v___x_654_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_694_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_694_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_694_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_694_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; 
if (lean_obj_tag(v_a_656_) == 1)
{
lean_object* v_mvarIds_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_693_; 
v_mvarIds_681_ = lean_ctor_get(v_a_656_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_693_ == 0)
{
v___x_683_ = v_a_656_;
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_mvarIds_681_);
lean_dec(v_a_656_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
if (lean_obj_tag(v_mvarIds_681_) == 1)
{
lean_object* v_tail_685_; 
v_tail_685_ = lean_ctor_get(v_mvarIds_681_, 1);
if (lean_obj_tag(v_tail_685_) == 0)
{
lean_object* v___x_687_; 
lean_dec(v_goal_636_);
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 4);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_mvarIds_681_);
v___x_687_ = v_reuseFailAlloc_692_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_688_);
v___x_690_ = v___x_658_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_681_, 2);
lean_del_object(v___x_683_);
lean_del_object(v___x_658_);
v___y_661_ = v_a_645_;
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
goto v___jp_660_;
}
}
else
{
lean_del_object(v___x_683_);
lean_dec(v_mvarIds_681_);
lean_del_object(v___x_658_);
v___y_661_ = v_a_645_;
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
goto v___jp_660_;
}
}
}
else
{
lean_del_object(v___x_658_);
lean_dec(v_a_656_);
v___y_661_ = v_a_645_;
v___y_662_ = v_a_646_;
v___y_663_ = v_a_647_;
v___y_664_ = v_a_648_;
goto v___jp_660_;
}
v___jp_660_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_MVarId_getType(v_goal_636_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__9);
v___x_668_ = l_Lean_MessageData_ofExpr(v_a_666_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___closed__11);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_671_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
return v___x_672_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_665_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_665_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_goal_636_);
v_a_695_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_655_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_655_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro___boxed(lean_object* v_goal_703_, lean_object* v_T_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_703_, v_T_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_T_704_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(lean_object* v_f_718_, lean_object* v_a_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___y_728_; lean_object* v___x_731_; uint8_t v_debug_732_; 
v___x_731_ = lean_st_ref_get(v___y_721_);
v_debug_732_ = lean_ctor_get_uint8(v___x_731_, sizeof(void*)*10);
lean_dec(v___x_731_);
if (v_debug_732_ == 0)
{
v___y_728_ = v___y_721_;
goto v___jp_727_;
}
else
{
lean_object* v___x_733_; 
lean_inc_ref(v_f_718_);
v___x_733_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_718_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec_ref_known(v___x_733_, 1);
lean_inc_ref(v_a_719_);
v___x_734_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
v___y_728_ = v___y_721_;
goto v___jp_727_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_a_719_);
lean_dec_ref(v_f_718_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_a_719_);
lean_dec_ref(v_f_718_);
v_a_743_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_733_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = l_Lean_Expr_app___override(v_f_718_, v_a_719_);
v___x_730_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_729_, v___y_728_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg___boxed(lean_object* v_f_751_, lean_object* v_a_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_751_, v_a_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(lean_object* v_f_761_, lean_object* v_a_u2081_762_, lean_object* v_a_u2082_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_761_, v_a_u2081_762_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_777_, v_a_u2082_763_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_778_;
}
else
{
lean_dec_ref(v_a_u2082_763_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0___boxed(lean_object* v_f_779_, lean_object* v_a_u2081_780_, lean_object* v_a_u2082_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_779_, v_a_u2081_780_, v_a_u2082_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(lean_object* v_f_795_, lean_object* v_a_u2081_796_, lean_object* v_a_u2082_797_, lean_object* v_a_u2083_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__0(v_f_795_, v_a_u2081_796_, v_a_u2082_797_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_812_, v_a_u2083_798_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_813_;
}
else
{
lean_dec_ref(v_a_u2083_798_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0___boxed(lean_object* v_f_814_, lean_object* v_a_u2081_815_, lean_object* v_a_u2082_816_, lean_object* v_a_u2083_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_814_, v_a_u2081_815_, v_a_u2082_816_, v_a_u2083_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(lean_object* v_goal_831_, lean_object* v_ent_832_, lean_object* v_00_u03c3s_833_, lean_object* v_H_834_, lean_object* v_T_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
lean_inc_ref(v_H_834_);
v___x_848_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_H_834_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
lean_inc_ref(v_T_835_);
v___x_850_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_T_835_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_898_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_898_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_898_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_898_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_890_; 
if (lean_obj_tag(v_a_849_) == 0)
{
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec_ref(v_T_835_);
lean_dec_ref(v_H_834_);
lean_dec_ref(v_00_u03c3s_833_);
lean_dec_ref(v_ent_832_);
lean_dec(v_goal_831_);
v___x_894_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_894_);
v___x_896_ = v___x_853_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_del_object(v___x_853_);
goto v___jp_892_;
}
}
else
{
lean_del_object(v___x_853_);
goto v___jp_892_;
}
v___jp_855_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_832_, v_00_u03c3s_833_, v___y_856_, v___y_857_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_831_, v_a_859_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_872_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_872_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v_a_861_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_868_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_860_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_860_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_goal_831_);
v_a_881_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_858_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_858_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_889_:
{
if (lean_obj_tag(v_a_851_) == 0)
{
v___y_856_ = v___y_890_;
v___y_857_ = v_T_835_;
goto v___jp_855_;
}
else
{
lean_object* v_val_891_; 
lean_dec_ref(v_T_835_);
v_val_891_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v_a_851_, 1);
v___y_856_ = v___y_890_;
v___y_857_ = v_val_891_;
goto v___jp_855_;
}
}
v___jp_892_:
{
if (lean_obj_tag(v_a_849_) == 0)
{
v___y_890_ = v_H_834_;
goto v___jp_889_;
}
else
{
lean_object* v_val_893_; 
lean_dec_ref(v_H_834_);
v_val_893_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v_a_849_, 1);
v___y_890_ = v_val_893_;
goto v___jp_889_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_a_849_);
lean_dec_ref(v_T_835_);
lean_dec_ref(v_H_834_);
lean_dec_ref(v_00_u03c3s_833_);
lean_dec_ref(v_ent_832_);
lean_dec(v_goal_831_);
v_a_899_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_850_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_850_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_T_835_);
lean_dec_ref(v_H_834_);
lean_dec_ref(v_00_u03c3s_833_);
lean_dec_ref(v_ent_832_);
lean_dec(v_goal_831_);
v_a_907_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_848_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_848_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT___boxed(lean_object** _args){
lean_object* v_goal_915_ = _args[0];
lean_object* v_ent_916_ = _args[1];
lean_object* v_00_u03c3s_917_ = _args[2];
lean_object* v_H_918_ = _args[3];
lean_object* v_T_919_ = _args[4];
lean_object* v_a_920_ = _args[5];
lean_object* v_a_921_ = _args[6];
lean_object* v_a_922_ = _args[7];
lean_object* v_a_923_ = _args[8];
lean_object* v_a_924_ = _args[9];
lean_object* v_a_925_ = _args[10];
lean_object* v_a_926_ = _args[11];
lean_object* v_a_927_ = _args[12];
lean_object* v_a_928_ = _args[13];
lean_object* v_a_929_ = _args[14];
lean_object* v_a_930_ = _args[15];
lean_object* v_a_931_ = _args[16];
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_915_, v_ent_916_, v_00_u03c3s_917_, v_H_918_, v_T_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(lean_object* v_f_933_, lean_object* v_a_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_f_933_, v_a_934_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___boxed(lean_object* v_f_948_, lean_object* v_a_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1(v_f_948_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_ks_967_; lean_object* v_vs_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_992_; 
v_ks_967_ = lean_ctor_get(v_x_963_, 0);
v_vs_968_ = lean_ctor_get(v_x_963_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_992_ == 0)
{
v___x_970_ = v_x_963_;
v_isShared_971_ = v_isSharedCheck_992_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_vs_968_);
lean_inc(v_ks_967_);
lean_dec(v_x_963_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_992_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_get_size(v_ks_967_);
v___x_973_ = lean_nat_dec_lt(v_x_964_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
lean_dec(v_x_964_);
v___x_974_ = lean_array_push(v_ks_967_, v_x_965_);
v___x_975_ = lean_array_push(v_vs_968_, v_x_966_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_975_);
lean_ctor_set(v___x_970_, 0, v___x_974_);
v___x_977_ = v___x_970_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
else
{
lean_object* v_k_x27_979_; uint8_t v___x_980_; 
v_k_x27_979_ = lean_array_fget_borrowed(v_ks_967_, v_x_964_);
v___x_980_ = l_Lean_instBEqMVarId_beq(v_x_965_, v_k_x27_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_982_; 
if (v_isShared_971_ == 0)
{
v___x_982_ = v___x_970_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_ks_967_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_vs_968_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_x_964_, v___x_983_);
lean_dec(v_x_964_);
v_x_963_ = v___x_982_;
v_x_964_ = v___x_984_;
goto _start;
}
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = lean_array_fset(v_ks_967_, v_x_964_, v_x_965_);
v___x_988_ = lean_array_fset(v_vs_968_, v_x_964_, v_x_966_);
lean_dec(v_x_964_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_988_);
lean_ctor_set(v___x_970_, 0, v___x_987_);
v___x_990_ = v___x_970_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_993_, lean_object* v_k_994_, lean_object* v_v_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_993_, v___x_996_, v_k_994_, v_v_995_);
return v___x_997_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; 
v___x_998_ = ((size_t)5ULL);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_shift_left(v___x_999_, v___x_998_);
return v___x_1000_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; 
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1003_ = lean_usize_sub(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1005_, size_t v_x_1006_, size_t v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_es_1010_; size_t v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; lean_object* v_j_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_es_1010_ = lean_ctor_get(v_x_1005_, 0);
v___x_1011_ = ((size_t)5ULL);
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1014_ = lean_usize_land(v_x_1006_, v___x_1013_);
v_j_1015_ = lean_usize_to_nat(v___x_1014_);
v___x_1016_ = lean_array_get_size(v_es_1010_);
v___x_1017_ = lean_nat_dec_lt(v_j_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_j_1015_);
lean_dec(v_x_1009_);
lean_dec(v_x_1008_);
return v_x_1005_;
}
else
{
lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1054_; 
lean_inc_ref(v_es_1010_);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_x_1005_, 0);
lean_dec(v_unused_1055_);
v___x_1019_ = v_x_1005_;
v_isShared_1020_ = v_isSharedCheck_1054_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_x_1005_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1054_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_v_1021_; lean_object* v___x_1022_; lean_object* v_xs_x27_1023_; lean_object* v___y_1025_; 
v_v_1021_ = lean_array_fget(v_es_1010_, v_j_1015_);
v___x_1022_ = lean_box(0);
v_xs_x27_1023_ = lean_array_fset(v_es_1010_, v_j_1015_, v___x_1022_);
switch(lean_obj_tag(v_v_1021_))
{
case 0:
{
lean_object* v_key_1030_; lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_key_1030_ = lean_ctor_get(v_v_1021_, 0);
v_val_1031_ = lean_ctor_get(v_v_1021_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_v_1021_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1033_ = v_v_1021_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_inc(v_key_1030_);
lean_dec(v_v_1021_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; 
v___x_1035_ = l_Lean_instBEqMVarId_beq(v_x_1008_, v_key_1030_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_del_object(v___x_1033_);
v___x_1036_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1030_, v_val_1031_, v_x_1008_, v_x_1009_);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
v___y_1025_ = v___x_1037_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_val_1031_);
lean_dec(v_key_1030_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v_x_1009_);
lean_ctor_set(v___x_1033_, 0, v_x_1008_);
v___x_1039_ = v___x_1033_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_x_1008_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_x_1009_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
v___y_1025_ = v___x_1039_;
goto v___jp_1024_;
}
}
}
}
case 1:
{
lean_object* v_node_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v_node_1042_ = lean_ctor_get(v_v_1021_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_v_1021_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1044_ = v_v_1021_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_node_1042_);
lean_dec(v_v_1021_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1046_ = lean_usize_shift_right(v_x_1006_, v___x_1011_);
v___x_1047_ = lean_usize_add(v_x_1007_, v___x_1012_);
v___x_1048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_node_1042_, v___x_1046_, v___x_1047_, v_x_1008_, v_x_1009_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
v___y_1025_ = v___x_1050_;
goto v___jp_1024_;
}
}
}
default: 
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_x_1008_);
lean_ctor_set(v___x_1053_, 1, v_x_1009_);
v___y_1025_ = v___x_1053_;
goto v___jp_1024_;
}
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_array_fset(v_xs_x27_1023_, v_j_1015_, v___y_1025_);
lean_dec(v_j_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1026_);
v___x_1028_ = v___x_1019_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
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
}
else
{
lean_object* v_ks_1056_; lean_object* v_vs_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1077_; 
v_ks_1056_ = lean_ctor_get(v_x_1005_, 0);
v_vs_1057_ = lean_ctor_get(v_x_1005_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1059_ = v_x_1005_;
v_isShared_1060_ = v_isSharedCheck_1077_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_vs_1057_);
lean_inc(v_ks_1056_);
lean_dec(v_x_1005_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1077_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_ks_1056_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_vs_1057_);
v___x_1062_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v_newNode_1063_; uint8_t v___y_1065_; size_t v___x_1071_; uint8_t v___x_1072_; 
v_newNode_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1062_, v_x_1008_, v_x_1009_);
v___x_1071_ = ((size_t)7ULL);
v___x_1072_ = lean_usize_dec_le(v___x_1071_, v_x_1007_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1063_);
v___x_1074_ = lean_unsigned_to_nat(4u);
v___x_1075_ = lean_nat_dec_lt(v___x_1073_, v___x_1074_);
lean_dec(v___x_1073_);
v___y_1065_ = v___x_1075_;
goto v___jp_1064_;
}
else
{
v___y_1065_ = v___x_1072_;
goto v___jp_1064_;
}
v___jp_1064_:
{
if (v___y_1065_ == 0)
{
lean_object* v_ks_1066_; lean_object* v_vs_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_ks_1066_ = lean_ctor_get(v_newNode_1063_, 0);
lean_inc_ref(v_ks_1066_);
v_vs_1067_ = lean_ctor_get(v_newNode_1063_, 1);
lean_inc_ref(v_vs_1067_);
lean_dec_ref(v_newNode_1063_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1007_, v_ks_1066_, v_vs_1067_, v___x_1068_, v___x_1069_);
lean_dec_ref(v_vs_1067_);
lean_dec_ref(v_ks_1066_);
return v___x_1070_;
}
else
{
return v_newNode_1063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1078_, lean_object* v_keys_1079_, lean_object* v_vals_1080_, lean_object* v_i_1081_, lean_object* v_entries_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_array_get_size(v_keys_1079_);
v___x_1084_ = lean_nat_dec_lt(v_i_1081_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec(v_i_1081_);
return v_entries_1082_;
}
else
{
lean_object* v_k_1085_; lean_object* v_v_1086_; uint64_t v___x_1087_; size_t v_h_1088_; size_t v___x_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v_h_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_k_1085_ = lean_array_fget_borrowed(v_keys_1079_, v_i_1081_);
v_v_1086_ = lean_array_fget_borrowed(v_vals_1080_, v_i_1081_);
v___x_1087_ = l_Lean_instHashableMVarId_hash(v_k_1085_);
v_h_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = ((size_t)5ULL);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = ((size_t)1ULL);
v___x_1092_ = lean_usize_sub(v_depth_1078_, v___x_1091_);
v___x_1093_ = lean_usize_mul(v___x_1089_, v___x_1092_);
v_h_1094_ = lean_usize_shift_right(v_h_1088_, v___x_1093_);
v___x_1095_ = lean_nat_add(v_i_1081_, v___x_1090_);
lean_dec(v_i_1081_);
lean_inc(v_v_1086_);
lean_inc(v_k_1085_);
v___x_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_entries_1082_, v_h_1094_, v_depth_1078_, v_k_1085_, v_v_1086_);
v_i_1081_ = v___x_1095_;
v_entries_1082_ = v___x_1096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1098_, lean_object* v_keys_1099_, lean_object* v_vals_1100_, lean_object* v_i_1101_, lean_object* v_entries_1102_){
_start:
{
size_t v_depth_boxed_1103_; lean_object* v_res_1104_; 
v_depth_boxed_1103_ = lean_unbox_usize(v_depth_1098_);
lean_dec(v_depth_1098_);
v_res_1104_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1103_, v_keys_1099_, v_vals_1100_, v_i_1101_, v_entries_1102_);
lean_dec_ref(v_vals_1100_);
lean_dec_ref(v_keys_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
size_t v_x_28835__boxed_1110_; size_t v_x_28836__boxed_1111_; lean_object* v_res_1112_; 
v_x_28835__boxed_1110_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_x_28836__boxed_1111_ = lean_unbox_usize(v_x_1107_);
lean_dec(v_x_1107_);
v_res_1112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1105_, v_x_28835__boxed_1110_, v_x_28836__boxed_1111_, v_x_1108_, v_x_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
uint64_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = l_Lean_instHashableMVarId_hash(v_x_1114_);
v___x_1117_ = lean_uint64_to_usize(v___x_1116_);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1113_, v___x_1117_, v___x_1118_, v_x_1114_, v_x_1115_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(lean_object* v_mvarId_1120_, lean_object* v_val_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v_mctx_1125_; lean_object* v_cache_1126_; lean_object* v_zetaDeltaFVarIds_1127_; lean_object* v_postponed_1128_; lean_object* v_diag_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1157_; 
v___x_1124_ = lean_st_ref_take(v___y_1122_);
v_mctx_1125_ = lean_ctor_get(v___x_1124_, 0);
v_cache_1126_ = lean_ctor_get(v___x_1124_, 1);
v_zetaDeltaFVarIds_1127_ = lean_ctor_get(v___x_1124_, 2);
v_postponed_1128_ = lean_ctor_get(v___x_1124_, 3);
v_diag_1129_ = lean_ctor_get(v___x_1124_, 4);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1131_ = v___x_1124_;
v_isShared_1132_ = v_isSharedCheck_1157_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_diag_1129_);
lean_inc(v_postponed_1128_);
lean_inc(v_zetaDeltaFVarIds_1127_);
lean_inc(v_cache_1126_);
lean_inc(v_mctx_1125_);
lean_dec(v___x_1124_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1157_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_depth_1133_; lean_object* v_levelAssignDepth_1134_; lean_object* v_lmvarCounter_1135_; lean_object* v_mvarCounter_1136_; lean_object* v_lDecls_1137_; lean_object* v_decls_1138_; lean_object* v_userNames_1139_; lean_object* v_lAssignment_1140_; lean_object* v_eAssignment_1141_; lean_object* v_dAssignment_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1156_; 
v_depth_1133_ = lean_ctor_get(v_mctx_1125_, 0);
v_levelAssignDepth_1134_ = lean_ctor_get(v_mctx_1125_, 1);
v_lmvarCounter_1135_ = lean_ctor_get(v_mctx_1125_, 2);
v_mvarCounter_1136_ = lean_ctor_get(v_mctx_1125_, 3);
v_lDecls_1137_ = lean_ctor_get(v_mctx_1125_, 4);
v_decls_1138_ = lean_ctor_get(v_mctx_1125_, 5);
v_userNames_1139_ = lean_ctor_get(v_mctx_1125_, 6);
v_lAssignment_1140_ = lean_ctor_get(v_mctx_1125_, 7);
v_eAssignment_1141_ = lean_ctor_get(v_mctx_1125_, 8);
v_dAssignment_1142_ = lean_ctor_get(v_mctx_1125_, 9);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_mctx_1125_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1144_ = v_mctx_1125_;
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_dAssignment_1142_);
lean_inc(v_eAssignment_1141_);
lean_inc(v_lAssignment_1140_);
lean_inc(v_userNames_1139_);
lean_inc(v_decls_1138_);
lean_inc(v_lDecls_1137_);
lean_inc(v_mvarCounter_1136_);
lean_inc(v_lmvarCounter_1135_);
lean_inc(v_levelAssignDepth_1134_);
lean_inc(v_depth_1133_);
lean_dec(v_mctx_1125_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(v_eAssignment_1141_, v_mvarId_1120_, v_val_1121_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 8, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_depth_1133_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_levelAssignDepth_1134_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_lmvarCounter_1135_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_mvarCounter_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_lDecls_1137_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_decls_1138_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_userNames_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v_lAssignment_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 9, v_dAssignment_1142_);
v___x_1148_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1148_);
v___x_1150_ = v___x_1131_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_cache_1126_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_zetaDeltaFVarIds_1127_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_postponed_1128_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_diag_1129_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_st_ref_set(v___y_1122_, v___x_1150_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg___boxed(lean_object* v_mvarId_1158_, lean_object* v_val_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_mvarId_1158_, v_val_1159_, v___y_1160_);
lean_dec(v___y_1160_);
return v_res_1162_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__3));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__6));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(lean_object* v_goal_1179_, lean_object* v_ent_1180_, lean_object* v_00_u03c3s_1181_, lean_object* v_H_1182_, lean_object* v_T_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_options_1196_; lean_object* v_inheritedTraceOptions_1197_; uint8_t v_hasTrace_1198_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v_cls_1226_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v_a_1240_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; 
v_options_1196_ = lean_ctor_get(v_a_1193_, 2);
v_inheritedTraceOptions_1197_ = lean_ctor_get(v_a_1193_, 13);
v_hasTrace_1198_ = lean_ctor_get_uint8(v_options_1196_, sizeof(void*)*1);
v_cls_1226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
if (v_hasTrace_1198_ == 0)
{
v___y_1289_ = v_a_1184_;
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
goto v___jp_1288_;
}
else
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1356_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1197_, v_options_1196_, v___x_1355_);
if (v___x_1356_ == 0)
{
v___y_1289_ = v_a_1184_;
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
goto v___jp_1288_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__7);
lean_inc(v_goal_1179_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_goal_1179_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1226_, v___x_1359_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
v___y_1289_ = v_a_1184_;
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
goto v___jp_1288_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_T_1183_);
lean_dec_ref(v_H_1182_);
lean_dec_ref(v_00_u03c3s_1181_);
lean_dec(v_goal_1179_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
v___jp_1199_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__2));
v___x_1213_ = l_Lean_Expr_constLevels_x21(v_ent_1180_);
v___x_1214_ = l_Lean_mkConst(v___x_1212_, v___x_1213_);
v___x_1215_ = l_Lean_mkAppB(v___x_1214_, v_00_u03c3s_1181_, v_H_1182_);
v___x_1216_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_goal_1179_, v___x_1215_, v___y_1209_);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1225_);
v___x_1218_ = v___x_1216_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1216_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_inc(v___y_1200_);
v___x_1220_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1200_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
v___jp_1227_:
{
if (v_a_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref(v_H_1182_);
lean_dec_ref(v_00_u03c3s_1181_);
v___x_1241_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(v_goal_1179_, v___y_1238_, v___y_1231_, v___y_1234_, v___y_1229_, v___y_1230_, v___y_1236_, v___y_1233_, v___y_1237_, v___y_1228_, v___y_1235_, v___y_1232_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1262_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
if (lean_obj_tag(v_a_1242_) == 1)
{
lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_T_1183_);
v_val_1246_ = lean_ctor_get(v_a_1242_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_a_1242_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1248_ = v_a_1242_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_dec(v_a_1242_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
lean_inc(v___y_1239_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_val_1246_);
lean_ctor_set(v___x_1250_, 1, v___y_1239_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 4);
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1252_);
v___x_1254_ = v___x_1244_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_a_1242_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_T_1183_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1258_);
v___x_1260_ = v___x_1244_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_T_1183_);
v_a_1263_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1241_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1241_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_options_1271_; uint8_t v_hasTrace_1272_; 
lean_dec_ref(v_T_1183_);
v_options_1271_ = lean_ctor_get(v___y_1235_, 2);
v_hasTrace_1272_ = lean_ctor_get_uint8(v_options_1271_, sizeof(void*)*1);
if (v_hasTrace_1272_ == 0)
{
v___y_1200_ = v___y_1239_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___y_1231_;
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1229_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1236_;
v___y_1207_ = v___y_1233_;
v___y_1208_ = v___y_1237_;
v___y_1209_ = v___y_1228_;
v___y_1210_ = v___y_1235_;
v___y_1211_ = v___y_1232_;
goto v___jp_1199_;
}
else
{
lean_object* v_inheritedTraceOptions_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_inheritedTraceOptions_1273_ = lean_ctor_get(v___y_1235_, 13);
v___x_1274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1275_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1273_, v_options_1271_, v___x_1274_);
if (v___x_1275_ == 0)
{
v___y_1200_ = v___y_1239_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___y_1231_;
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1229_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1236_;
v___y_1207_ = v___y_1233_;
v___y_1208_ = v___y_1237_;
v___y_1209_ = v___y_1228_;
v___y_1210_ = v___y_1235_;
v___y_1211_ = v___y_1232_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__4);
lean_inc(v_goal_1179_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_goal_1179_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1226_, v___x_1278_, v___y_1237_, v___y_1228_, v___y_1235_, v___y_1232_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_dec_ref_known(v___x_1279_, 1);
v___y_1200_ = v___y_1239_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___y_1231_;
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1229_;
v___y_1205_ = v___y_1230_;
v___y_1206_ = v___y_1236_;
v___y_1207_ = v___y_1233_;
v___y_1208_ = v___y_1237_;
v___y_1209_ = v___y_1228_;
v___y_1210_ = v___y_1235_;
v___y_1211_ = v___y_1232_;
goto v___jp_1199_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_H_1182_);
lean_dec_ref(v_00_u03c3s_1181_);
lean_dec(v_goal_1179_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
v___jp_1288_:
{
lean_object* v___x_1300_; uint8_t v_foApprox_1301_; uint8_t v_ctxApprox_1302_; uint8_t v_quasiPatternApprox_1303_; uint8_t v_constApprox_1304_; uint8_t v_isDefEqStuckEx_1305_; uint8_t v_unificationHints_1306_; uint8_t v_proofIrrelevance_1307_; uint8_t v_offsetCnstrs_1308_; uint8_t v_transparency_1309_; uint8_t v_etaStruct_1310_; uint8_t v_univApprox_1311_; uint8_t v_iota_1312_; uint8_t v_beta_1313_; uint8_t v_proj_1314_; uint8_t v_zeta_1315_; uint8_t v_zetaDelta_1316_; uint8_t v_zetaUnused_1317_; uint8_t v_zetaHave_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1354_; 
v___x_1300_ = l_Lean_Meta_Context_config(v___y_1296_);
v_foApprox_1301_ = lean_ctor_get_uint8(v___x_1300_, 0);
v_ctxApprox_1302_ = lean_ctor_get_uint8(v___x_1300_, 1);
v_quasiPatternApprox_1303_ = lean_ctor_get_uint8(v___x_1300_, 2);
v_constApprox_1304_ = lean_ctor_get_uint8(v___x_1300_, 3);
v_isDefEqStuckEx_1305_ = lean_ctor_get_uint8(v___x_1300_, 4);
v_unificationHints_1306_ = lean_ctor_get_uint8(v___x_1300_, 5);
v_proofIrrelevance_1307_ = lean_ctor_get_uint8(v___x_1300_, 6);
v_offsetCnstrs_1308_ = lean_ctor_get_uint8(v___x_1300_, 8);
v_transparency_1309_ = lean_ctor_get_uint8(v___x_1300_, 9);
v_etaStruct_1310_ = lean_ctor_get_uint8(v___x_1300_, 10);
v_univApprox_1311_ = lean_ctor_get_uint8(v___x_1300_, 11);
v_iota_1312_ = lean_ctor_get_uint8(v___x_1300_, 12);
v_beta_1313_ = lean_ctor_get_uint8(v___x_1300_, 13);
v_proj_1314_ = lean_ctor_get_uint8(v___x_1300_, 14);
v_zeta_1315_ = lean_ctor_get_uint8(v___x_1300_, 15);
v_zetaDelta_1316_ = lean_ctor_get_uint8(v___x_1300_, 16);
v_zetaUnused_1317_ = lean_ctor_get_uint8(v___x_1300_, 17);
v_zetaHave_1318_ = lean_ctor_get_uint8(v___x_1300_, 18);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1320_ = v___x_1300_;
v_isShared_1321_ = v_isSharedCheck_1354_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v___x_1300_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1354_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v_trackZetaDelta_1322_; lean_object* v_zetaDeltaSet_1323_; lean_object* v_lctx_1324_; lean_object* v_localInstances_1325_; lean_object* v_defEqCtx_x3f_1326_; lean_object* v_synthPendingDepth_1327_; lean_object* v_canUnfold_x3f_1328_; uint8_t v_univApprox_1329_; uint8_t v_inTypeClassResolution_1330_; uint8_t v_cacheInferType_1331_; uint8_t v___x_1332_; lean_object* v___x_1334_; 
v_trackZetaDelta_1322_ = lean_ctor_get_uint8(v___y_1296_, sizeof(void*)*7);
v_zetaDeltaSet_1323_ = lean_ctor_get(v___y_1296_, 1);
v_lctx_1324_ = lean_ctor_get(v___y_1296_, 2);
v_localInstances_1325_ = lean_ctor_get(v___y_1296_, 3);
v_defEqCtx_x3f_1326_ = lean_ctor_get(v___y_1296_, 4);
v_synthPendingDepth_1327_ = lean_ctor_get(v___y_1296_, 5);
v_canUnfold_x3f_1328_ = lean_ctor_get(v___y_1296_, 6);
v_univApprox_1329_ = lean_ctor_get_uint8(v___y_1296_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1330_ = lean_ctor_get_uint8(v___y_1296_, sizeof(void*)*7 + 2);
v_cacheInferType_1331_ = lean_ctor_get_uint8(v___y_1296_, sizeof(void*)*7 + 3);
v___x_1332_ = 1;
if (v_isShared_1321_ == 0)
{
v___x_1334_ = v___x_1320_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 0, v_foApprox_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 1, v_ctxApprox_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 2, v_quasiPatternApprox_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 3, v_constApprox_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 4, v_isDefEqStuckEx_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 5, v_unificationHints_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 6, v_proofIrrelevance_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 8, v_offsetCnstrs_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 9, v_transparency_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 10, v_etaStruct_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 11, v_univApprox_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 12, v_iota_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 13, v_beta_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 14, v_proj_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 15, v_zeta_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 16, v_zetaDelta_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 17, v_zetaUnused_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1353_, 18, v_zetaHave_1318_);
v___x_1334_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
uint64_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_ctor_set_uint8(v___x_1334_, 7, v___x_1332_);
v___x_1335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1334_);
v___x_1336_ = lean_box(0);
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred___closed__5));
v___x_1338_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1338_, 0, v___x_1334_);
lean_ctor_set_uint64(v___x_1338_, sizeof(void*)*1, v___x_1335_);
lean_inc(v_canUnfold_x3f_1328_);
lean_inc(v_synthPendingDepth_1327_);
lean_inc(v_defEqCtx_x3f_1326_);
lean_inc_ref(v_localInstances_1325_);
lean_inc_ref(v_lctx_1324_);
lean_inc(v_zetaDeltaSet_1323_);
v___x_1339_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_zetaDeltaSet_1323_);
lean_ctor_set(v___x_1339_, 2, v_lctx_1324_);
lean_ctor_set(v___x_1339_, 3, v_localInstances_1325_);
lean_ctor_set(v___x_1339_, 4, v_defEqCtx_x3f_1326_);
lean_ctor_set(v___x_1339_, 5, v_synthPendingDepth_1327_);
lean_ctor_set(v___x_1339_, 6, v_canUnfold_x3f_1328_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7, v_trackZetaDelta_1322_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 1, v_univApprox_1329_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1330_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 3, v_cacheInferType_1331_);
lean_inc_ref(v_T_1183_);
lean_inc_ref(v_H_1182_);
v___x_1340_ = l_Lean_Meta_Sym_isDefEqS(v_H_1182_, v_T_1183_, v___x_1332_, v___x_1332_, v___x_1337_, v___x_1337_, v___y_1294_, v___y_1295_, v___x_1339_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec_ref_known(v___x_1339_, 7);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; uint8_t v___x_1342_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = lean_unbox(v_a_1341_);
lean_dec(v_a_1341_);
v___y_1228_ = v___y_1297_;
v___y_1229_ = v___y_1292_;
v___y_1230_ = v___y_1293_;
v___y_1231_ = v___y_1290_;
v___y_1232_ = v___y_1299_;
v___y_1233_ = v___y_1295_;
v___y_1234_ = v___y_1291_;
v___y_1235_ = v___y_1298_;
v___y_1236_ = v___y_1294_;
v___y_1237_ = v___y_1296_;
v___y_1238_ = v___y_1289_;
v___y_1239_ = v___x_1336_;
v_a_1240_ = v___x_1342_;
goto v___jp_1227_;
}
else
{
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1343_; uint8_t v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1344_ = lean_unbox(v_a_1343_);
lean_dec(v_a_1343_);
v___y_1228_ = v___y_1297_;
v___y_1229_ = v___y_1292_;
v___y_1230_ = v___y_1293_;
v___y_1231_ = v___y_1290_;
v___y_1232_ = v___y_1299_;
v___y_1233_ = v___y_1295_;
v___y_1234_ = v___y_1291_;
v___y_1235_ = v___y_1298_;
v___y_1236_ = v___y_1294_;
v___y_1237_ = v___y_1296_;
v___y_1238_ = v___y_1289_;
v___y_1239_ = v___x_1336_;
v_a_1240_ = v___x_1344_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_T_1183_);
lean_dec_ref(v_H_1182_);
lean_dec_ref(v_00_u03c3s_1181_);
lean_dec(v_goal_1179_);
v_a_1345_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1340_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
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
lean_object* v_goal_1369_ = _args[0];
lean_object* v_ent_1370_ = _args[1];
lean_object* v_00_u03c3s_1371_ = _args[2];
lean_object* v_H_1372_ = _args[3];
lean_object* v_T_1373_ = _args[4];
lean_object* v_a_1374_ = _args[5];
lean_object* v_a_1375_ = _args[6];
lean_object* v_a_1376_ = _args[7];
lean_object* v_a_1377_ = _args[8];
lean_object* v_a_1378_ = _args[9];
lean_object* v_a_1379_ = _args[10];
lean_object* v_a_1380_ = _args[11];
lean_object* v_a_1381_ = _args[12];
lean_object* v_a_1382_ = _args[13];
lean_object* v_a_1383_ = _args[14];
lean_object* v_a_1384_ = _args[15];
lean_object* v_a_1385_ = _args[16];
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(v_goal_1369_, v_ent_1370_, v_00_u03c3s_1371_, v_H_1372_, v_T_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec_ref(v_ent_1370_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0(lean_object* v_mvarId_1387_, lean_object* v_val_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___redArg(v_mvarId_1387_, v_val_1388_, v___y_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0___boxed(lean_object* v_mvarId_1402_, lean_object* v_val_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0(v_mvarId_1402_, v_val_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0(lean_object* v_00_u03b2_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0___redArg(v_x_1418_, v_x_1419_, v_x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1422_, lean_object* v_x_1423_, size_t v_x_1424_, size_t v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___redArg(v_x_1423_, v_x_1424_, v_x_1425_, v_x_1426_, v_x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
size_t v_x_29457__boxed_1435_; size_t v_x_29458__boxed_1436_; lean_object* v_res_1437_; 
v_x_29457__boxed_1435_ = lean_unbox_usize(v_x_1431_);
lean_dec(v_x_1431_);
v_x_29458__boxed_1436_ = lean_unbox_usize(v_x_1432_);
lean_dec(v_x_1432_);
v_res_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1(v_00_u03b2_1429_, v_x_1430_, v_x_29457__boxed_1435_, v_x_29458__boxed_1436_, v_x_1433_, v_x_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1438_, lean_object* v_n_1439_, lean_object* v_k_1440_, lean_object* v_v_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1439_, v_k_1440_, v_v_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1443_, size_t v_depth_1444_, lean_object* v_keys_1445_, lean_object* v_vals_1446_, lean_object* v_heq_1447_, lean_object* v_i_1448_, lean_object* v_entries_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1444_, v_keys_1445_, v_vals_1446_, v_i_1448_, v_entries_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1451_, lean_object* v_depth_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_heq_1455_, lean_object* v_i_1456_, lean_object* v_entries_1457_){
_start:
{
size_t v_depth_boxed_1458_; lean_object* v_res_1459_; 
v_depth_boxed_1458_ = lean_unbox_usize(v_depth_1452_);
lean_dec(v_depth_1452_);
v_res_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1451_, v_depth_boxed_1458_, v_keys_1453_, v_vals_1454_, v_heq_1455_, v_i_1456_, v_entries_1457_);
lean_dec_ref(v_vals_1454_);
lean_dec_ref(v_keys_1453_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1461_, v_x_1462_, v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(lean_object* v_args_1466_, lean_object* v_endIdx_1467_, lean_object* v_b_1468_, lean_object* v_i_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_le(v_endIdx_1467_, v_i_1469_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = l_Lean_instInhabitedExpr;
v___x_1479_ = lean_array_get_borrowed(v___x_1478_, v_args_1466_, v_i_1469_);
lean_inc(v___x_1479_);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_1468_, v___x_1479_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_i_1469_, v___x_1482_);
lean_dec(v_i_1469_);
v_b_1468_ = v_a_1481_;
v_i_1469_ = v___x_1483_;
goto _start;
}
else
{
lean_dec(v_i_1469_);
return v___x_1480_;
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_i_1469_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_b_1468_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg___boxed(lean_object* v_args_1486_, lean_object* v_endIdx_1487_, lean_object* v_b_1488_, lean_object* v_i_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1486_, v_endIdx_1487_, v_b_1488_, v_i_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_endIdx_1487_);
lean_dec_ref(v_args_1486_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(lean_object* v_f_1498_, lean_object* v_args_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get_size(v_args_1499_);
v___x_1514_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1499_, v___x_1513_, v_f_1498_, v___x_1512_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1___boxed(lean_object* v_f_1515_, lean_object* v_args_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_f_1515_, v_args_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_args_1516_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_f_1530_, lean_object* v_a_u2081_1531_, lean_object* v_a_u2082_1532_, lean_object* v_a_u2083_1533_, lean_object* v_a_u2084_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_f_1530_, v_a_u2081_1531_, v_a_u2082_1532_, v_a_u2083_1533_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_1548_, v_a_u2084_1534_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1549_;
}
else
{
lean_dec_ref(v_a_u2084_1534_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_f_1550_ = _args[0];
lean_object* v_a_u2081_1551_ = _args[1];
lean_object* v_a_u2082_1552_ = _args[2];
lean_object* v_a_u2083_1553_ = _args[3];
lean_object* v_a_u2084_1554_ = _args[4];
lean_object* v___y_1555_ = _args[5];
lean_object* v___y_1556_ = _args[6];
lean_object* v___y_1557_ = _args[7];
lean_object* v___y_1558_ = _args[8];
lean_object* v___y_1559_ = _args[9];
lean_object* v___y_1560_ = _args[10];
lean_object* v___y_1561_ = _args[11];
lean_object* v___y_1562_ = _args[12];
lean_object* v___y_1563_ = _args[13];
lean_object* v___y_1564_ = _args[14];
lean_object* v___y_1565_ = _args[15];
lean_object* v___y_1566_ = _args[16];
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_1550_, v_a_u2081_1551_, v_a_u2082_1552_, v_a_u2083_1553_, v_a_u2084_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_1568_, lean_object* v_a_u2081_1569_, lean_object* v_a_u2082_1570_, lean_object* v_a_u2083_1571_, lean_object* v_a_u2084_1572_, lean_object* v_a_u2085_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_f_1568_, v_a_u2081_1569_, v_a_u2082_1570_, v_a_u2083_1571_, v_a_u2084_1572_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_a_1587_, v_a_u2085_1573_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1588_;
}
else
{
lean_dec_ref(v_a_u2085_1573_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object** _args){
lean_object* v_f_1589_ = _args[0];
lean_object* v_a_u2081_1590_ = _args[1];
lean_object* v_a_u2082_1591_ = _args[2];
lean_object* v_a_u2083_1592_ = _args[3];
lean_object* v_a_u2084_1593_ = _args[4];
lean_object* v_a_u2085_1594_ = _args[5];
lean_object* v___y_1595_ = _args[6];
lean_object* v___y_1596_ = _args[7];
lean_object* v___y_1597_ = _args[8];
lean_object* v___y_1598_ = _args[9];
lean_object* v___y_1599_ = _args[10];
lean_object* v___y_1600_ = _args[11];
lean_object* v___y_1601_ = _args[12];
lean_object* v___y_1602_ = _args[13];
lean_object* v___y_1603_ = _args[14];
lean_object* v___y_1604_ = _args[15];
lean_object* v___y_1605_ = _args[16];
lean_object* v___y_1606_ = _args[17];
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_1589_, v_a_u2081_1590_, v_a_u2082_1591_, v_a_u2083_1592_, v_a_u2084_1593_, v_a_u2085_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_1608_, lean_object* v_head_1609_, lean_object* v_H_1610_, lean_object* v_00_u03c3s_1611_, lean_object* v_ent_1612_, lean_object* v_args_1613_, lean_object* v_wpConst_1614_, lean_object* v_m_1615_, lean_object* v_ps_1616_, lean_object* v_instWP_1617_, lean_object* v_00_u03b1_1618_, lean_object* v_e_x27_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_1614_, v_m_1615_, v_ps_1616_, v_instWP_1617_, v_00_u03b1_1618_, v_e_x27_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = lean_unsigned_to_nat(2u);
v___x_1635_ = lean_array_set(v_args_1613_, v___x_1634_, v_a_1633_);
v___x_1636_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_1609_, v___x_1635_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec_ref(v___x_1635_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_1612_, v_00_u03c3s_1611_, v_H_1610_, v_a_1637_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1608_, v_a_1639_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1640_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_goal_1608_);
v_a_1641_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1638_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1638_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v_ent_1612_);
lean_dec_ref(v_00_u03c3s_1611_);
lean_dec_ref(v_H_1610_);
lean_dec(v_goal_1608_);
v_a_1649_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1636_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1636_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_args_1613_);
lean_dec_ref(v_ent_1612_);
lean_dec_ref(v_00_u03c3s_1611_);
lean_dec_ref(v_H_1610_);
lean_dec_ref(v_head_1609_);
lean_dec(v_goal_1608_);
v_a_1657_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1632_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1632_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object** _args){
lean_object* v_goal_1665_ = _args[0];
lean_object* v_head_1666_ = _args[1];
lean_object* v_H_1667_ = _args[2];
lean_object* v_00_u03c3s_1668_ = _args[3];
lean_object* v_ent_1669_ = _args[4];
lean_object* v_args_1670_ = _args[5];
lean_object* v_wpConst_1671_ = _args[6];
lean_object* v_m_1672_ = _args[7];
lean_object* v_ps_1673_ = _args[8];
lean_object* v_instWP_1674_ = _args[9];
lean_object* v_00_u03b1_1675_ = _args[10];
lean_object* v_e_x27_1676_ = _args[11];
lean_object* v_a_1677_ = _args[12];
lean_object* v_a_1678_ = _args[13];
lean_object* v_a_1679_ = _args[14];
lean_object* v_a_1680_ = _args[15];
lean_object* v_a_1681_ = _args[16];
lean_object* v_a_1682_ = _args[17];
lean_object* v_a_1683_ = _args[18];
lean_object* v_a_1684_ = _args[19];
lean_object* v_a_1685_ = _args[20];
lean_object* v_a_1686_ = _args[21];
lean_object* v_a_1687_ = _args[22];
lean_object* v_a_1688_ = _args[23];
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_1665_, v_head_1666_, v_H_1667_, v_00_u03c3s_1668_, v_ent_1669_, v_args_1670_, v_wpConst_1671_, v_m_1672_, v_ps_1673_, v_instWP_1674_, v_00_u03b1_1675_, v_e_x27_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(lean_object* v_args_1690_, lean_object* v_endIdx_1691_, lean_object* v_b_1692_, lean_object* v_i_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___redArg(v_args_1690_, v_endIdx_1691_, v_b_1692_, v_i_1693_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2___boxed(lean_object* v_args_1707_, lean_object* v_endIdx_1708_, lean_object* v_b_1709_, lean_object* v_i_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1_spec__2(v_args_1707_, v_endIdx_1708_, v_b_1709_, v_i_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_endIdx_1708_);
lean_dec_ref(v_args_1707_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(lean_object* v_revArgs_1724_, lean_object* v_start_1725_, lean_object* v_b_1726_, lean_object* v_i_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_le(v_i_1727_, v_start_1725_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v_i_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = lean_unsigned_to_nat(1u);
v_i_1737_ = lean_nat_sub(v_i_1727_, v___x_1736_);
lean_dec(v_i_1727_);
v___x_1738_ = l_Lean_instInhabitedExpr;
v___x_1739_ = lean_array_get_borrowed(v___x_1738_, v_revArgs_1724_, v_i_1737_);
lean_inc(v___x_1739_);
v___x_1740_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0_spec__1___redArg(v_b_1726_, v___x_1739_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_b_1726_ = v_a_1741_;
v_i_1727_ = v_i_1737_;
goto _start;
}
else
{
lean_dec(v_i_1737_);
return v___x_1740_;
}
}
else
{
lean_object* v___x_1743_; 
lean_dec(v_i_1727_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_b_1726_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_1744_, lean_object* v_start_1745_, lean_object* v_b_1746_, lean_object* v_i_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1744_, v_start_1745_, v_b_1746_, v_i_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v_start_1745_);
lean_dec_ref(v_revArgs_1744_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(lean_object* v_f_1756_, lean_object* v_revArgs_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_array_get_size(v_revArgs_1757_);
v___x_1772_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1757_, v___x_1770_, v_f_1756_, v___x_1771_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0___boxed(lean_object* v_f_1773_, lean_object* v_revArgs_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_f_1773_, v_revArgs_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_revArgs_1774_);
return v_res_1787_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__0));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(lean_object* v_goal_1791_, lean_object* v_head_1792_, lean_object* v_H_1793_, lean_object* v_00_u03c3s_1794_, lean_object* v_ent_1795_, lean_object* v_args_1796_, lean_object* v_wpConst_1797_, lean_object* v_m_1798_, lean_object* v_ps_1799_, lean_object* v_instWP_1800_, lean_object* v_00_u03b1_1801_, lean_object* v_e_1802_, lean_object* v_f_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
if (lean_obj_tag(v_f_1803_) == 8)
{
lean_object* v_declName_1816_; lean_object* v_type_1817_; lean_object* v_value_1818_; lean_object* v_body_1819_; uint8_t v_nondep_1820_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v_options_1900_; uint8_t v_hasTrace_1901_; 
v_declName_1816_ = lean_ctor_get(v_f_1803_, 0);
lean_inc(v_declName_1816_);
v_type_1817_ = lean_ctor_get(v_f_1803_, 1);
lean_inc_ref(v_type_1817_);
v_value_1818_ = lean_ctor_get(v_f_1803_, 2);
lean_inc_ref(v_value_1818_);
v_body_1819_ = lean_ctor_get(v_f_1803_, 3);
lean_inc_ref(v_body_1819_);
v_nondep_1820_ = lean_ctor_get_uint8(v_f_1803_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_f_1803_, 4);
v_options_1900_ = lean_ctor_get(v_a_1813_, 2);
v_hasTrace_1901_ = lean_ctor_get_uint8(v_options_1900_, sizeof(void*)*1);
if (v_hasTrace_1901_ == 0)
{
v___y_1822_ = v_a_1804_;
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
goto v___jp_1821_;
}
else
{
lean_object* v_inheritedTraceOptions_1902_; lean_object* v_cls_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v_inheritedTraceOptions_1902_ = lean_ctor_get(v_a_1813_, 13);
v_cls_1903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_1905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1902_, v_options_1900_, v___x_1904_);
if (v___x_1905_ == 0)
{
v___y_1822_ = v_a_1804_;
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
goto v___jp_1821_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___closed__1);
lean_inc(v_declName_1816_);
v___x_1907_ = l_Lean_MessageData_ofName(v_declName_1816_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_1903_, v___x_1908_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_dec_ref_known(v___x_1909_, 1);
v___y_1822_ = v_a_1804_;
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
goto v___jp_1821_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_body_1819_);
lean_dec_ref(v_value_1818_);
lean_dec_ref(v_type_1817_);
lean_dec(v_declName_1816_);
lean_dec_ref(v_e_1802_);
lean_dec_ref(v_00_u03b1_1801_);
lean_dec_ref(v_instWP_1800_);
lean_dec_ref(v_ps_1799_);
lean_dec_ref(v_m_1798_);
lean_dec_ref(v_wpConst_1797_);
lean_dec_ref(v_args_1796_);
lean_dec_ref(v_ent_1795_);
lean_dec_ref(v_00_u03c3s_1794_);
lean_dec_ref(v_H_1793_);
lean_dec_ref(v_head_1792_);
lean_dec(v_goal_1791_);
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
v___jp_1821_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = l_Lean_Expr_getAppNumArgs(v_e_1802_);
v___x_1834_ = lean_mk_empty_array_with_capacity(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1802_, v___x_1834_);
v___x_1836_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0(v_body_1819_, v___x_1835_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_wpConst_1797_, v_m_1798_, v_ps_1799_, v_instWP_1800_, v_00_u03b1_1801_, v_a_1837_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = lean_unsigned_to_nat(2u);
v___x_1841_ = lean_array_set(v_args_1796_, v___x_1840_, v_a_1839_);
v___x_1842_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__1(v_head_1792_, v___x_1841_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v___x_1841_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT_spec__0(v_ent_1795_, v_00_u03c3s_1794_, v_H_1793_, v_a_1843_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = l_Lean_Expr_letE___override(v_declName_1816_, v_type_1817_, v_value_1818_, v_a_1845_, v_nondep_1820_);
v___x_1847_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1791_, v___x_1846_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1859_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1859_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1859_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_a_1848_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1855_);
v___x_1857_ = v___x_1850_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1847_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1847_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_value_1818_);
lean_dec_ref(v_type_1817_);
lean_dec(v_declName_1816_);
lean_dec(v_goal_1791_);
v_a_1868_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1844_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1844_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_value_1818_);
lean_dec_ref(v_type_1817_);
lean_dec(v_declName_1816_);
lean_dec_ref(v_ent_1795_);
lean_dec_ref(v_00_u03c3s_1794_);
lean_dec_ref(v_H_1793_);
lean_dec(v_goal_1791_);
v_a_1876_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1842_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1842_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_value_1818_);
lean_dec_ref(v_type_1817_);
lean_dec(v_declName_1816_);
lean_dec_ref(v_args_1796_);
lean_dec_ref(v_ent_1795_);
lean_dec_ref(v_00_u03c3s_1794_);
lean_dec_ref(v_H_1793_);
lean_dec_ref(v_head_1792_);
lean_dec(v_goal_1791_);
v_a_1884_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1838_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1838_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_value_1818_);
lean_dec_ref(v_type_1817_);
lean_dec(v_declName_1816_);
lean_dec_ref(v_00_u03b1_1801_);
lean_dec_ref(v_instWP_1800_);
lean_dec_ref(v_ps_1799_);
lean_dec_ref(v_m_1798_);
lean_dec_ref(v_wpConst_1797_);
lean_dec_ref(v_args_1796_);
lean_dec_ref(v_ent_1795_);
lean_dec_ref(v_00_u03c3s_1794_);
lean_dec_ref(v_H_1793_);
lean_dec_ref(v_head_1792_);
lean_dec(v_goal_1791_);
v_a_1892_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1836_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1836_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v_f_1803_);
lean_dec_ref(v_e_1802_);
lean_dec_ref(v_00_u03b1_1801_);
lean_dec_ref(v_instWP_1800_);
lean_dec_ref(v_ps_1799_);
lean_dec_ref(v_m_1798_);
lean_dec_ref(v_wpConst_1797_);
lean_dec_ref(v_args_1796_);
lean_dec_ref(v_ent_1795_);
lean_dec_ref(v_00_u03c3s_1794_);
lean_dec_ref(v_H_1793_);
lean_dec_ref(v_head_1792_);
lean_dec(v_goal_1791_);
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist___boxed(lean_object** _args){
lean_object* v_goal_1920_ = _args[0];
lean_object* v_head_1921_ = _args[1];
lean_object* v_H_1922_ = _args[2];
lean_object* v_00_u03c3s_1923_ = _args[3];
lean_object* v_ent_1924_ = _args[4];
lean_object* v_args_1925_ = _args[5];
lean_object* v_wpConst_1926_ = _args[6];
lean_object* v_m_1927_ = _args[7];
lean_object* v_ps_1928_ = _args[8];
lean_object* v_instWP_1929_ = _args[9];
lean_object* v_00_u03b1_1930_ = _args[10];
lean_object* v_e_1931_ = _args[11];
lean_object* v_f_1932_ = _args[12];
lean_object* v_a_1933_ = _args[13];
lean_object* v_a_1934_ = _args[14];
lean_object* v_a_1935_ = _args[15];
lean_object* v_a_1936_ = _args[16];
lean_object* v_a_1937_ = _args[17];
lean_object* v_a_1938_ = _args[18];
lean_object* v_a_1939_ = _args[19];
lean_object* v_a_1940_ = _args[20];
lean_object* v_a_1941_ = _args[21];
lean_object* v_a_1942_ = _args[22];
lean_object* v_a_1943_ = _args[23];
lean_object* v_a_1944_ = _args[24];
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_1920_, v_head_1921_, v_H_1922_, v_00_u03c3s_1923_, v_ent_1924_, v_args_1925_, v_wpConst_1926_, v_m_1927_, v_ps_1928_, v_instWP_1929_, v_00_u03b1_1930_, v_e_1931_, v_f_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(lean_object* v_revArgs_1946_, lean_object* v_start_1947_, lean_object* v_b_1948_, lean_object* v_i_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___redArg(v_revArgs_1946_, v_start_1947_, v_b_1948_, v_i_1949_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0___boxed(lean_object* v_revArgs_1963_, lean_object* v_start_1964_, lean_object* v_b_1965_, lean_object* v_i_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist_spec__0_spec__0(v_revArgs_1963_, v_start_1964_, v_b_1965_, v_i_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v_start_1964_);
lean_dec_ref(v_revArgs_1963_);
return v_res_1979_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0(void){
_start:
{
uint8_t v___x_1980_; uint64_t v___x_1981_; 
v___x_1980_ = 2;
v___x_1981_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__1));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__3));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(lean_object* v_goal_1988_, lean_object* v_head_1989_, lean_object* v_H_1990_, lean_object* v_00_u03c3s_1991_, lean_object* v_ent_1992_, lean_object* v_args_1993_, lean_object* v_wpConst_1994_, lean_object* v_m_1995_, lean_object* v_ps_1996_, lean_object* v_instWP_1997_, lean_object* v_00_u03b1_1998_, lean_object* v_e_1999_, lean_object* v_excessArgs_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___x_2013_; 
lean_inc_ref(v_e_1999_);
v___x_2013_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_1999_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2165_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2165_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2165_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
if (lean_obj_tag(v_a_2014_) == 1)
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2016_);
v_val_2018_ = lean_ctor_get(v_a_2014_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2020_ = v_a_2014_;
v_isShared_2021_ = v_isSharedCheck_2160_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v_a_2014_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2160_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; uint8_t v_foApprox_2023_; uint8_t v_ctxApprox_2024_; uint8_t v_quasiPatternApprox_2025_; uint8_t v_constApprox_2026_; uint8_t v_isDefEqStuckEx_2027_; uint8_t v_unificationHints_2028_; uint8_t v_proofIrrelevance_2029_; uint8_t v_assignSyntheticOpaque_2030_; uint8_t v_offsetCnstrs_2031_; uint8_t v_etaStruct_2032_; uint8_t v_univApprox_2033_; uint8_t v_iota_2034_; uint8_t v_beta_2035_; uint8_t v_proj_2036_; uint8_t v_zeta_2037_; uint8_t v_zetaDelta_2038_; uint8_t v_zetaUnused_2039_; uint8_t v_zetaHave_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2159_; 
v___x_2022_ = l_Lean_Meta_Context_config(v_a_2008_);
v_foApprox_2023_ = lean_ctor_get_uint8(v___x_2022_, 0);
v_ctxApprox_2024_ = lean_ctor_get_uint8(v___x_2022_, 1);
v_quasiPatternApprox_2025_ = lean_ctor_get_uint8(v___x_2022_, 2);
v_constApprox_2026_ = lean_ctor_get_uint8(v___x_2022_, 3);
v_isDefEqStuckEx_2027_ = lean_ctor_get_uint8(v___x_2022_, 4);
v_unificationHints_2028_ = lean_ctor_get_uint8(v___x_2022_, 5);
v_proofIrrelevance_2029_ = lean_ctor_get_uint8(v___x_2022_, 6);
v_assignSyntheticOpaque_2030_ = lean_ctor_get_uint8(v___x_2022_, 7);
v_offsetCnstrs_2031_ = lean_ctor_get_uint8(v___x_2022_, 8);
v_etaStruct_2032_ = lean_ctor_get_uint8(v___x_2022_, 10);
v_univApprox_2033_ = lean_ctor_get_uint8(v___x_2022_, 11);
v_iota_2034_ = lean_ctor_get_uint8(v___x_2022_, 12);
v_beta_2035_ = lean_ctor_get_uint8(v___x_2022_, 13);
v_proj_2036_ = lean_ctor_get_uint8(v___x_2022_, 14);
v_zeta_2037_ = lean_ctor_get_uint8(v___x_2022_, 15);
v_zetaDelta_2038_ = lean_ctor_get_uint8(v___x_2022_, 16);
v_zetaUnused_2039_ = lean_ctor_get_uint8(v___x_2022_, 17);
v_zetaHave_2040_ = lean_ctor_get_uint8(v___x_2022_, 18);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2042_ = v___x_2022_;
v_isShared_2043_ = v_isSharedCheck_2159_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v___x_2022_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2159_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v_trackZetaDelta_2044_; lean_object* v_zetaDeltaSet_2045_; lean_object* v_lctx_2046_; lean_object* v_localInstances_2047_; lean_object* v_defEqCtx_x3f_2048_; lean_object* v_synthPendingDepth_2049_; lean_object* v_canUnfold_x3f_2050_; uint8_t v_univApprox_2051_; uint8_t v_inTypeClassResolution_2052_; uint8_t v_cacheInferType_2053_; uint8_t v___x_2054_; lean_object* v_config_2056_; 
v_trackZetaDelta_2044_ = lean_ctor_get_uint8(v_a_2008_, sizeof(void*)*7);
v_zetaDeltaSet_2045_ = lean_ctor_get(v_a_2008_, 1);
v_lctx_2046_ = lean_ctor_get(v_a_2008_, 2);
v_localInstances_2047_ = lean_ctor_get(v_a_2008_, 3);
v_defEqCtx_x3f_2048_ = lean_ctor_get(v_a_2008_, 4);
v_synthPendingDepth_2049_ = lean_ctor_get(v_a_2008_, 5);
v_canUnfold_x3f_2050_ = lean_ctor_get(v_a_2008_, 6);
v_univApprox_2051_ = lean_ctor_get_uint8(v_a_2008_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2052_ = lean_ctor_get_uint8(v_a_2008_, sizeof(void*)*7 + 2);
v_cacheInferType_2053_ = lean_ctor_get_uint8(v_a_2008_, sizeof(void*)*7 + 3);
v___x_2054_ = 2;
if (v_isShared_2043_ == 0)
{
v_config_2056_ = v___x_2042_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 0, v_foApprox_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 1, v_ctxApprox_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 2, v_quasiPatternApprox_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 3, v_constApprox_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 4, v_isDefEqStuckEx_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 5, v_unificationHints_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 6, v_proofIrrelevance_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 7, v_assignSyntheticOpaque_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 8, v_offsetCnstrs_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 10, v_etaStruct_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 11, v_univApprox_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 12, v_iota_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 13, v_beta_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 14, v_proj_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 15, v_zeta_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 16, v_zetaDelta_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 17, v_zetaUnused_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, 18, v_zetaHave_2040_);
v_config_2056_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
uint64_t v___x_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v_key_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_ctor_set_uint8(v_config_2056_, 9, v___x_2054_);
v___x_2057_ = l_Lean_Meta_Context_configKey(v_a_2008_);
v___x_2058_ = 3ULL;
v___x_2059_ = lean_uint64_shift_right(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_uint64_shift_left(v___x_2059_, v___x_2058_);
v___x_2061_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__0);
v_key_2062_ = lean_uint64_lor(v___x_2060_, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2063_, 0, v_config_2056_);
lean_ctor_set_uint64(v___x_2063_, sizeof(void*)*1, v_key_2062_);
lean_inc(v_canUnfold_x3f_2050_);
lean_inc(v_synthPendingDepth_2049_);
lean_inc(v_defEqCtx_x3f_2048_);
lean_inc_ref(v_localInstances_2047_);
lean_inc_ref(v_lctx_2046_);
lean_inc(v_zetaDeltaSet_2045_);
v___x_2064_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_zetaDeltaSet_2045_);
lean_ctor_set(v___x_2064_, 2, v_lctx_2046_);
lean_ctor_set(v___x_2064_, 3, v_localInstances_2047_);
lean_ctor_set(v___x_2064_, 4, v_defEqCtx_x3f_2048_);
lean_ctor_set(v___x_2064_, 5, v_synthPendingDepth_2049_);
lean_ctor_set(v___x_2064_, 6, v_canUnfold_x3f_2050_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*7, v_trackZetaDelta_2044_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*7 + 1, v_univApprox_2051_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2052_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*7 + 3, v_cacheInferType_2053_);
v___x_2065_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_1999_, v___x_2064_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec_ref_known(v___x_2064_, 7);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
if (lean_obj_tag(v_a_2066_) == 1)
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_2020_);
lean_dec(v_val_2018_);
lean_dec_ref(v_excessArgs_2000_);
lean_dec_ref(v_e_1999_);
v_val_2067_ = lean_ctor_get(v_a_2066_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2069_ = v_a_2066_;
v_isShared_2070_ = v_isSharedCheck_2104_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v_a_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2104_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2067_, v_a_2007_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_1988_, v_head_1989_, v_H_1990_, v_00_u03c3s_1991_, v_ent_1992_, v_args_1993_, v_wpConst_1994_, v_m_1995_, v_ps_1996_, v_instWP_1997_, v_00_u03b1_1998_, v_a_2072_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2087_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2087_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2087_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v_a_2074_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2080_);
v___x_2082_ = v___x_2069_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2082_);
v___x_2084_ = v___x_2076_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_del_object(v___x_2069_);
v_a_2088_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2073_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2073_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_del_object(v___x_2069_);
lean_dec_ref(v_00_u03b1_1998_);
lean_dec_ref(v_instWP_1997_);
lean_dec_ref(v_ps_1996_);
lean_dec_ref(v_m_1995_);
lean_dec_ref(v_wpConst_1994_);
lean_dec_ref(v_args_1993_);
lean_dec_ref(v_ent_1992_);
lean_dec_ref(v_00_u03c3s_1991_);
lean_dec_ref(v_H_1990_);
lean_dec_ref(v_head_1989_);
lean_dec(v_goal_1988_);
v_a_2096_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2071_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2071_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v_a_2066_);
lean_dec_ref(v_00_u03b1_1998_);
lean_dec_ref(v_wpConst_1994_);
lean_dec_ref(v_args_1993_);
lean_dec_ref(v_ent_1992_);
lean_dec_ref(v_H_1990_);
lean_dec_ref(v_head_1989_);
v___x_2105_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(v_val_2018_, v_m_1995_, v_00_u03c3s_1991_, v_ps_1996_, v_instWP_1997_, v_excessArgs_2000_, v_a_2002_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__2);
v___x_2108_ = l_Lean_indentExpr(v_e_1999_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2109_);
v___x_2111_ = v___x_2020_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2106_, v_goal_1988_, v___x_2111_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2132_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2132_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2132_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
if (lean_obj_tag(v_a_2113_) == 1)
{
lean_object* v_mvarIds_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v___x_2108_);
v_mvarIds_2117_ = lean_ctor_get(v_a_2113_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_a_2113_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2119_ = v_a_2113_;
v_isShared_2120_ = v_isSharedCheck_2128_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_mvarIds_2117_);
lean_dec(v_a_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2128_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 4);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_mvarIds_2117_);
v___x_2122_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2123_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_2115_);
lean_dec(v_a_2113_);
v___x_2129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___closed__4);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2108_);
v___x_2131_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_2130_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
return v___x_2131_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___x_2108_);
v_a_2133_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2112_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2112_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2020_);
lean_dec_ref(v_e_1999_);
lean_dec(v_goal_1988_);
v_a_2142_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2105_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2105_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_del_object(v___x_2020_);
lean_dec(v_val_2018_);
lean_dec_ref(v_excessArgs_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_00_u03b1_1998_);
lean_dec_ref(v_instWP_1997_);
lean_dec_ref(v_ps_1996_);
lean_dec_ref(v_m_1995_);
lean_dec_ref(v_wpConst_1994_);
lean_dec_ref(v_args_1993_);
lean_dec_ref(v_ent_1992_);
lean_dec_ref(v_00_u03c3s_1991_);
lean_dec_ref(v_H_1990_);
lean_dec_ref(v_head_1989_);
lean_dec(v_goal_1988_);
v_a_2150_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2065_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2065_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec(v_a_2014_);
lean_dec_ref(v_excessArgs_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_00_u03b1_1998_);
lean_dec_ref(v_instWP_1997_);
lean_dec_ref(v_ps_1996_);
lean_dec_ref(v_m_1995_);
lean_dec_ref(v_wpConst_1994_);
lean_dec_ref(v_args_1993_);
lean_dec_ref(v_ent_1992_);
lean_dec_ref(v_00_u03c3s_1991_);
lean_dec_ref(v_H_1990_);
lean_dec_ref(v_head_1989_);
lean_dec(v_goal_1988_);
v___x_2161_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2161_);
v___x_2163_ = v___x_2016_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_excessArgs_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_00_u03b1_1998_);
lean_dec_ref(v_instWP_1997_);
lean_dec_ref(v_ps_1996_);
lean_dec_ref(v_m_1995_);
lean_dec_ref(v_wpConst_1994_);
lean_dec_ref(v_args_1993_);
lean_dec_ref(v_ent_1992_);
lean_dec_ref(v_00_u03c3s_1991_);
lean_dec_ref(v_H_1990_);
lean_dec_ref(v_head_1989_);
lean_dec(v_goal_1988_);
v_a_2166_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2013_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2013_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit___boxed(lean_object** _args){
lean_object* v_goal_2174_ = _args[0];
lean_object* v_head_2175_ = _args[1];
lean_object* v_H_2176_ = _args[2];
lean_object* v_00_u03c3s_2177_ = _args[3];
lean_object* v_ent_2178_ = _args[4];
lean_object* v_args_2179_ = _args[5];
lean_object* v_wpConst_2180_ = _args[6];
lean_object* v_m_2181_ = _args[7];
lean_object* v_ps_2182_ = _args[8];
lean_object* v_instWP_2183_ = _args[9];
lean_object* v_00_u03b1_2184_ = _args[10];
lean_object* v_e_2185_ = _args[11];
lean_object* v_excessArgs_2186_ = _args[12];
lean_object* v_a_2187_ = _args[13];
lean_object* v_a_2188_ = _args[14];
lean_object* v_a_2189_ = _args[15];
lean_object* v_a_2190_ = _args[16];
lean_object* v_a_2191_ = _args[17];
lean_object* v_a_2192_ = _args[18];
lean_object* v_a_2193_ = _args[19];
lean_object* v_a_2194_ = _args[20];
lean_object* v_a_2195_ = _args[21];
lean_object* v_a_2196_ = _args[22];
lean_object* v_a_2197_ = _args[23];
lean_object* v_a_2198_ = _args[24];
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_2174_, v_head_2175_, v_H_2176_, v_00_u03c3s_2177_, v_ent_2178_, v_args_2179_, v_wpConst_2180_, v_m_2181_, v_ps_2182_, v_instWP_2183_, v_00_u03b1_2184_, v_e_2185_, v_excessArgs_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__0));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(lean_object* v_goal_2203_, lean_object* v_head_2204_, lean_object* v_H_2205_, lean_object* v_00_u03c3s_2206_, lean_object* v_ent_2207_, lean_object* v_args_2208_, lean_object* v_wpConst_2209_, lean_object* v_m_2210_, lean_object* v_ps_2211_, lean_object* v_instWP_2212_, lean_object* v_00_u03b1_2213_, lean_object* v_e_2214_, lean_object* v_f_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Expr_fvarId_x3f(v_f_2215_);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2336_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2336_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2336_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
uint8_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = 0;
lean_inc(v_val_2229_);
v___x_2234_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_2229_, v___x_2233_, v_a_2223_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2327_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2327_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2327_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
if (lean_obj_tag(v_a_2235_) == 1)
{
lean_object* v_val_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2237_);
v_val_2239_ = lean_ctor_get(v_a_2235_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2235_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2241_ = v_a_2235_;
v_isShared_2242_ = v_isSharedCheck_2322_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_val_2239_);
lean_dec(v_a_2235_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2322_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v_options_2294_; uint8_t v_hasTrace_2295_; 
v_options_2294_ = lean_ctor_get(v_a_2225_, 2);
v_hasTrace_2295_ = lean_ctor_get_uint8(v_options_2294_, sizeof(void*)*1);
if (v_hasTrace_2295_ == 0)
{
lean_dec(v_val_2229_);
v___y_2244_ = v_a_2216_;
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
goto v___jp_2243_;
}
else
{
lean_object* v_inheritedTraceOptions_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_inheritedTraceOptions_2296_ = lean_ctor_get(v_a_2225_, 13);
v___x_2297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___x_2298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_2299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2296_, v_options_2294_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_dec(v_val_2229_);
v___y_2244_ = v_a_2216_;
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
goto v___jp_2243_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_FVarId_getUserName___redArg(v_val_2229_, v_a_2223_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___closed__1);
v___x_2303_ = l_Lean_MessageData_ofName(v_a_2301_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___x_2297_, v___x_2304_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_dec_ref_known(v___x_2305_, 1);
v___y_2244_ = v_a_2216_;
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
goto v___jp_2243_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_del_object(v___x_2241_);
lean_dec(v_val_2239_);
lean_del_object(v___x_2231_);
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
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
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_del_object(v___x_2241_);
lean_dec(v_val_2239_);
lean_del_object(v___x_2231_);
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v_a_2314_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2300_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2300_);
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
}
v___jp_2243_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2255_ = l_Lean_Expr_getAppNumArgs(v_e_2214_);
v___x_2256_ = lean_mk_empty_array_with_capacity(v___x_2255_);
lean_dec(v___x_2255_);
v___x_2257_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_2214_, v___x_2256_);
v___x_2258_ = l_Lean_Expr_betaRev(v_val_2239_, v___x_2257_, v___x_2233_, v___x_2233_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_2258_, v___y_2250_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2203_, v_head_2204_, v_H_2205_, v_00_u03c3s_2206_, v_ent_2207_, v_args_2208_, v_wpConst_2209_, v_m_2210_, v_ps_2211_, v_instWP_2212_, v_00_u03b1_2213_, v_a_2260_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2277_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2277_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2262_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 4);
lean_ctor_set(v___x_2231_, 0, v___x_2267_);
v___x_2269_ = v___x_2231_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2269_);
v___x_2271_ = v___x_2241_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2271_);
v___x_2273_ = v___x_2264_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_del_object(v___x_2241_);
lean_del_object(v___x_2231_);
v_a_2278_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2261_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2261_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_del_object(v___x_2241_);
lean_del_object(v___x_2231_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v_a_2286_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2259_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2259_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
lean_dec(v_a_2235_);
lean_del_object(v___x_2231_);
lean_dec(v_val_2229_);
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v___x_2323_ = lean_box(0);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2323_);
v___x_2325_ = v___x_2237_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_del_object(v___x_2231_);
lean_dec(v_val_2229_);
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v_a_2328_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2234_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2234_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v___x_2228_);
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_00_u03b1_2213_);
lean_dec_ref(v_instWP_2212_);
lean_dec_ref(v_ps_2211_);
lean_dec_ref(v_m_2210_);
lean_dec_ref(v_wpConst_2209_);
lean_dec_ref(v_args_2208_);
lean_dec_ref(v_ent_2207_);
lean_dec_ref(v_00_u03c3s_2206_);
lean_dec_ref(v_H_2205_);
lean_dec_ref(v_head_2204_);
lean_dec(v_goal_2203_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta___boxed(lean_object** _args){
lean_object* v_goal_2339_ = _args[0];
lean_object* v_head_2340_ = _args[1];
lean_object* v_H_2341_ = _args[2];
lean_object* v_00_u03c3s_2342_ = _args[3];
lean_object* v_ent_2343_ = _args[4];
lean_object* v_args_2344_ = _args[5];
lean_object* v_wpConst_2345_ = _args[6];
lean_object* v_m_2346_ = _args[7];
lean_object* v_ps_2347_ = _args[8];
lean_object* v_instWP_2348_ = _args[9];
lean_object* v_00_u03b1_2349_ = _args[10];
lean_object* v_e_2350_ = _args[11];
lean_object* v_f_2351_ = _args[12];
lean_object* v_a_2352_ = _args[13];
lean_object* v_a_2353_ = _args[14];
lean_object* v_a_2354_ = _args[15];
lean_object* v_a_2355_ = _args[16];
lean_object* v_a_2356_ = _args[17];
lean_object* v_a_2357_ = _args[18];
lean_object* v_a_2358_ = _args[19];
lean_object* v_a_2359_ = _args[20];
lean_object* v_a_2360_ = _args[21];
lean_object* v_a_2361_ = _args[22];
lean_object* v_a_2362_ = _args[23];
lean_object* v_a_2363_ = _args[24];
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_2339_, v_head_2340_, v_H_2341_, v_00_u03c3s_2342_, v_ent_2343_, v_args_2344_, v_wpConst_2345_, v_m_2346_, v_ps_2347_, v_instWP_2348_, v_00_u03b1_2349_, v_e_2350_, v_f_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_f_2351_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(lean_object* v_cls_2365_, lean_object* v_____do__lift_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_options_2379_; uint8_t v_hasTrace_2380_; 
v_options_2379_ = lean_ctor_get(v___y_2376_, 2);
v_hasTrace_2380_ = lean_ctor_get_uint8(v_options_2379_, sizeof(void*)*1);
if (v_hasTrace_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec(v_cls_2365_);
v___x_2381_ = lean_box(v_hasTrace_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
v___x_2384_ = l_Lean_Name_append(v___x_2383_, v_cls_2365_);
v___x_2385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2366_, v_options_2379_, v___x_2384_);
lean_dec(v___x_2384_);
v___x_2386_ = lean_box(v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(lean_object* v_cls_2388_, lean_object* v_____do__lift_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_2388_, v_____do__lift_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec_ref(v_____do__lift_2389_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
if (lean_obj_tag(v_a_2403_) == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = l_List_reverse___redArg(v_a_2404_);
return v___x_2405_;
}
else
{
lean_object* v_head_2406_; lean_object* v_tail_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
v_head_2406_ = lean_ctor_get(v_a_2403_, 0);
v_tail_2407_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v_a_2403_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_tail_2407_);
lean_inc(v_head_2406_);
lean_dec(v_a_2403_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = l_Lean_MessageData_ofExpr(v_head_2406_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v_a_2404_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2404_);
v___x_2413_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
v_a_2403_ = v_tail_2407_;
v_a_2404_ = v___x_2413_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_2428_ = l_Lean_stringToMessageData(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_2446_ = l_Lean_stringToMessageData(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_goal_2458_, lean_object* v_e_2459_, lean_object* v_excessArgs_2460_, lean_object* v_m_2461_, lean_object* v_00_u03c3s_2462_, lean_object* v_ps_2463_, lean_object* v_instWP_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2539_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2731_; lean_object* v_f_2757_; uint8_t v___x_2758_; 
v_f_2757_ = l_Lean_Expr_getAppFn(v_e_2459_);
v___x_2758_ = l_Lean_Expr_isConst(v_f_2757_);
if (v___x_2758_ == 0)
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Lean_Expr_isFVar(v_f_2757_);
lean_dec_ref(v_f_2757_);
v___y_2731_ = v___x_2759_;
goto v___jp_2730_;
}
else
{
lean_dec_ref(v_f_2757_);
v___y_2731_ = v___x_2758_;
goto v___jp_2730_;
}
v___jp_2477_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_e_2459_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
v___jp_2480_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_2494_ = l_Lean_indentExpr(v_e_2459_);
lean_inc_ref(v___x_2494_);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_inc_ref(v___y_2481_);
v___x_2497_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v___y_2481_, v_goal_2458_, v___x_2496_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2529_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2529_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2529_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
if (lean_obj_tag(v_a_2498_) == 1)
{
lean_object* v_mvarIds_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___y_2481_);
v_mvarIds_2502_ = lean_ctor_get(v_a_2498_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2504_ = v_a_2498_;
v_isShared_2505_ = v_isSharedCheck_2512_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_mvarIds_2502_);
lean_dec(v_a_2498_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2512_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 4);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_mvarIds_2502_);
v___x_2507_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2507_);
v___x_2509_ = v___x_2500_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v_expr_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_del_object(v___x_2500_);
lean_dec(v_a_2498_);
v_expr_2513_ = lean_ctor_get(v___y_2481_, 0);
lean_inc_ref(v_expr_2513_);
lean_dec_ref(v___y_2481_);
v___x_2514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_2515_ = l_Lean_MessageData_ofExpr(v_expr_2513_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2494_);
v___x_2520_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__1___redArg(v___x_2519_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v___x_2494_);
lean_dec_ref(v___y_2481_);
v_a_2530_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2497_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2497_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___y_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
v___jp_2544_:
{
lean_object* v___x_2559_; 
lean_inc(v_goal_2458_);
lean_inc_ref(v___y_2547_);
v___x_2559_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(v___y_2547_, v_goal_2458_, v_excessArgs_2460_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
if (lean_obj_tag(v_a_2560_) == 1)
{
lean_object* v_options_2561_; uint8_t v_hasTrace_2562_; 
lean_dec_ref(v___y_2547_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_options_2561_ = lean_ctor_get(v___y_2557_, 2);
v_hasTrace_2562_ = lean_ctor_get_uint8(v_options_2561_, sizeof(void*)*1);
if (v_hasTrace_2562_ == 0)
{
lean_object* v_val_2563_; 
lean_dec(v___y_2545_);
v_val_2563_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v_a_2560_, 1);
v___y_2539_ = v_val_2563_;
goto v___jp_2538_;
}
else
{
lean_object* v_val_2564_; lean_object* v_inheritedTraceOptions_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v_val_2564_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v_a_2560_, 1);
v_inheritedTraceOptions_2565_ = lean_ctor_get(v___y_2557_, 13);
v___x_2566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__8));
lean_inc(v___y_2545_);
v___x_2567_ = l_Lean_Name_append(v___x_2566_, v___y_2545_);
v___x_2568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2565_, v_options_2561_, v___x_2567_);
lean_dec(v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec(v___y_2545_);
v___y_2539_ = v_val_2564_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_2570_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2545_, v___x_2569_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_dec_ref_known(v___x_2570_, 1);
v___y_2539_ = v_val_2564_;
goto v___jp_2538_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_val_2564_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
else
{
lean_object* v___x_2579_; 
lean_dec(v_a_2560_);
v___x_2579_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v___y_2547_, v_m_2461_, v_00_u03c3s_2462_, v_ps_2463_, v_instWP_2464_, v_excessArgs_2460_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v_inheritedTraceOptions_2581_; lean_object* v___x_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_inheritedTraceOptions_2581_ = lean_ctor_get(v___y_2557_, 13);
lean_inc_ref(v___y_2546_);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
lean_inc(v___y_2552_);
lean_inc_ref(v___y_2551_);
lean_inc(v___y_2550_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
lean_inc_ref(v_inheritedTraceOptions_2581_);
v___x_2582_ = lean_apply_13(v___y_2546_, v_inheritedTraceOptions_2581_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, lean_box(0));
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint8_t v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
if (v___x_2584_ == 0)
{
lean_dec(v___y_2545_);
v___y_2481_ = v_a_2580_;
v___y_2482_ = v___y_2548_;
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
goto v___jp_2480_;
}
else
{
lean_object* v_expr_2585_; lean_object* v___x_2586_; 
v_expr_2585_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc_ref(v_expr_2585_);
v___x_2586_ = lean_infer_type(v_expr_2585_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_2589_ = l_Lean_MessageData_ofExpr(v_a_2587_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2545_, v___x_2590_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2481_ = v_a_2580_;
v___y_2482_ = v___y_2548_;
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
goto v___jp_2480_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2580_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2580_);
lean_dec(v___y_2545_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2600_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2586_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2586_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_a_2580_);
lean_dec(v___y_2545_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2608_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2582_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2582_);
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
lean_dec(v___y_2545_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2616_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2579_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2579_);
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
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2545_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2624_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2559_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2559_);
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
v___jp_2632_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___y_2637_);
lean_ctor_set(v___x_2649_, 1, v___y_2648_);
lean_inc(v___y_2640_);
v___x_2650_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v___y_2640_, v___x_2649_, v___y_2638_, v___y_2641_, v___y_2634_, v___y_2639_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_dec_ref_known(v___x_2650_, 1);
v___y_2545_ = v___y_2640_;
v___y_2546_ = v___y_2636_;
v___y_2547_ = v___y_2644_;
v___y_2548_ = v___y_2646_;
v___y_2549_ = v___y_2642_;
v___y_2550_ = v___y_2633_;
v___y_2551_ = v___y_2647_;
v___y_2552_ = v___y_2635_;
v___y_2553_ = v___y_2643_;
v___y_2554_ = v___y_2645_;
v___y_2555_ = v___y_2638_;
v___y_2556_ = v___y_2641_;
v___y_2557_ = v___y_2634_;
v___y_2558_ = v___y_2639_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2640_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
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
v___jp_2659_:
{
lean_object* v_specThms_2673_; lean_object* v___x_2674_; 
v_specThms_2673_ = lean_ctor_get(v___y_2662_, 0);
lean_inc_ref(v_e_2459_);
v___x_2674_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_specThms_2673_, v_e_2459_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2721_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2721_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2721_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
if (lean_obj_tag(v_a_2675_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec(v___y_2660_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec(v_goal_2458_);
v_a_2679_ = lean_ctor_get(v_a_2675_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v_a_2675_, 1);
v___x_2680_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2680_, 0, v_e_2459_);
lean_ctor_set(v___x_2680_, 1, v_m_2461_);
lean_ctor_set(v___x_2680_, 2, v_a_2679_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2680_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v_inheritedTraceOptions_2685_; lean_object* v___x_2686_; 
lean_del_object(v___x_2677_);
v_a_2684_ = lean_ctor_get(v_a_2675_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v_a_2675_, 1);
v_inheritedTraceOptions_2685_ = lean_ctor_get(v___y_2671_, 13);
lean_inc_ref(v___y_2661_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc(v___y_2663_);
lean_inc_ref(v___y_2662_);
lean_inc_ref(v_inheritedTraceOptions_2685_);
v___x_2686_ = lean_apply_13(v___y_2661_, v_inheritedTraceOptions_2685_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, lean_box(0));
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; uint8_t v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = lean_unbox(v_a_2687_);
lean_dec(v_a_2687_);
if (v___x_2688_ == 0)
{
v___y_2545_ = v___y_2660_;
v___y_2546_ = v___y_2661_;
v___y_2547_ = v_a_2684_;
v___y_2548_ = v___y_2662_;
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
goto v___jp_2544_;
}
else
{
lean_object* v_proof_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_proof_2689_ = lean_ctor_get(v_a_2684_, 1);
v___x_2690_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
lean_inc_ref(v_e_2459_);
v___x_2691_ = l_Lean_MessageData_ofExpr(v_e_2459_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
switch(lean_obj_tag(v_proof_2689_))
{
case 0:
{
lean_object* v_declName_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_declName_2695_ = lean_ctor_get(v_proof_2689_, 0);
v___x_2696_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
lean_inc(v_declName_2695_);
v___x_2697_ = l_Lean_MessageData_ofName(v_declName_2695_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___y_2633_ = v___y_2664_;
v___y_2634_ = v___y_2671_;
v___y_2635_ = v___y_2666_;
v___y_2636_ = v___y_2661_;
v___y_2637_ = v___x_2694_;
v___y_2638_ = v___y_2669_;
v___y_2639_ = v___y_2672_;
v___y_2640_ = v___y_2660_;
v___y_2641_ = v___y_2670_;
v___y_2642_ = v___y_2663_;
v___y_2643_ = v___y_2667_;
v___y_2644_ = v_a_2684_;
v___y_2645_ = v___y_2668_;
v___y_2646_ = v___y_2662_;
v___y_2647_ = v___y_2665_;
v___y_2648_ = v___x_2698_;
goto v___jp_2632_;
}
case 1:
{
lean_object* v_fvarId_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_fvarId_2699_ = lean_ctor_get(v_proof_2689_, 0);
v___x_2700_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
lean_inc(v_fvarId_2699_);
v___x_2701_ = l_Lean_mkFVar(v_fvarId_2699_);
v___x_2702_ = l_Lean_MessageData_ofExpr(v___x_2701_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2700_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___y_2633_ = v___y_2664_;
v___y_2634_ = v___y_2671_;
v___y_2635_ = v___y_2666_;
v___y_2636_ = v___y_2661_;
v___y_2637_ = v___x_2694_;
v___y_2638_ = v___y_2669_;
v___y_2639_ = v___y_2672_;
v___y_2640_ = v___y_2660_;
v___y_2641_ = v___y_2670_;
v___y_2642_ = v___y_2663_;
v___y_2643_ = v___y_2667_;
v___y_2644_ = v_a_2684_;
v___y_2645_ = v___y_2668_;
v___y_2646_ = v___y_2662_;
v___y_2647_ = v___y_2665_;
v___y_2648_ = v___x_2703_;
goto v___jp_2632_;
}
default: 
{
lean_object* v_ref_2704_; lean_object* v_proof_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_ref_2704_ = lean_ctor_get(v_proof_2689_, 1);
v_proof_2705_ = lean_ctor_get(v_proof_2689_, 2);
v___x_2706_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
lean_inc(v_ref_2704_);
v___x_2707_ = l_Lean_MessageData_ofSyntax(v_ref_2704_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
lean_inc_ref(v_proof_2705_);
v___x_2711_ = l_Lean_MessageData_ofExpr(v_proof_2705_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___y_2633_ = v___y_2664_;
v___y_2634_ = v___y_2671_;
v___y_2635_ = v___y_2666_;
v___y_2636_ = v___y_2661_;
v___y_2637_ = v___x_2694_;
v___y_2638_ = v___y_2669_;
v___y_2639_ = v___y_2672_;
v___y_2640_ = v___y_2660_;
v___y_2641_ = v___y_2670_;
v___y_2642_ = v___y_2663_;
v___y_2643_ = v___y_2667_;
v___y_2644_ = v_a_2684_;
v___y_2645_ = v___y_2668_;
v___y_2646_ = v___y_2662_;
v___y_2647_ = v___y_2665_;
v___y_2648_ = v___x_2712_;
goto v___jp_2632_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_a_2684_);
lean_dec(v___y_2660_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2713_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2686_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2686_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___y_2660_);
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2722_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2674_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2674_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
v___jp_2730_:
{
if (v___y_2731_ == 0)
{
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec(v_goal_2458_);
goto v___jp_2477_;
}
else
{
lean_object* v_inheritedTraceOptions_2732_; lean_object* v_cls_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v_a_2736_; uint8_t v___x_2737_; 
v_inheritedTraceOptions_2732_ = lean_ctor_get(v_a_2474_, 13);
v_cls_2733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
v___f_2734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22));
v___x_2735_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_cls_2733_, v_inheritedTraceOptions_2732_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = lean_unbox(v_a_2736_);
lean_dec(v_a_2736_);
if (v___x_2737_ == 0)
{
v___y_2660_ = v_cls_2733_;
v___y_2661_ = v___f_2734_;
v___y_2662_ = v_a_2465_;
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
goto v___jp_2659_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24);
lean_inc_ref(v_e_2459_);
v___x_2739_ = l_Lean_MessageData_ofExpr(v_e_2459_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__26);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_inc_ref(v_excessArgs_2460_);
v___x_2743_ = lean_array_to_list(v_excessArgs_2460_);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_2743_, v___x_2744_);
v___x_2746_ = l_Lean_MessageData_ofList(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2742_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_2733_, v___x_2747_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_dec_ref_known(v___x_2748_, 1);
v___y_2660_ = v_cls_2733_;
v___y_2661_ = v___f_2734_;
v___y_2662_ = v_a_2465_;
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
goto v___jp_2659_;
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_instWP_2464_);
lean_dec_ref(v_ps_2463_);
lean_dec_ref(v_00_u03c3s_2462_);
lean_dec_ref(v_m_2461_);
lean_dec_ref(v_excessArgs_2460_);
lean_dec_ref(v_e_2459_);
lean_dec(v_goal_2458_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object** _args){
lean_object* v_goal_2760_ = _args[0];
lean_object* v_e_2761_ = _args[1];
lean_object* v_excessArgs_2762_ = _args[2];
lean_object* v_m_2763_ = _args[3];
lean_object* v_00_u03c3s_2764_ = _args[4];
lean_object* v_ps_2765_ = _args[5];
lean_object* v_instWP_2766_ = _args[6];
lean_object* v_a_2767_ = _args[7];
lean_object* v_a_2768_ = _args[8];
lean_object* v_a_2769_ = _args[9];
lean_object* v_a_2770_ = _args[10];
lean_object* v_a_2771_ = _args[11];
lean_object* v_a_2772_ = _args[12];
lean_object* v_a_2773_ = _args[13];
lean_object* v_a_2774_ = _args[14];
lean_object* v_a_2775_ = _args[15];
lean_object* v_a_2776_ = _args[16];
lean_object* v_a_2777_ = _args[17];
lean_object* v_a_2778_ = _args[18];
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_goal_2760_, v_e_2761_, v_excessArgs_2762_, v_m_2763_, v_00_u03c3s_2764_, v_ps_2765_, v_instWP_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
lean_inc(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
v___x_2793_ = lean_apply_12(v_x_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed(lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0(v_x_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(lean_object* v_mvarId_2808_, lean_object* v_x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___f_2822_; lean_object* v___x_2823_; 
lean_inc(v___y_2816_);
lean_inc_ref(v___y_2815_);
lean_inc(v___y_2814_);
lean_inc_ref(v___y_2813_);
lean_inc(v___y_2812_);
lean_inc(v___y_2811_);
lean_inc_ref(v___y_2810_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2822_, 0, v_x_2809_);
lean_closure_set(v___f_2822_, 1, v___y_2810_);
lean_closure_set(v___f_2822_, 2, v___y_2811_);
lean_closure_set(v___f_2822_, 3, v___y_2812_);
lean_closure_set(v___f_2822_, 4, v___y_2813_);
lean_closure_set(v___f_2822_, 5, v___y_2814_);
lean_closure_set(v___f_2822_, 6, v___y_2815_);
lean_closure_set(v___f_2822_, 7, v___y_2816_);
v___x_2823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2808_, v___f_2822_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2823_) == 0)
{
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg___boxed(lean_object* v_mvarId_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_2832_, v_x_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(lean_object* v_00_u03b1_2847_, lean_object* v_mvarId_2848_, lean_object* v_x_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_mvarId_2848_, v_x_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_mvarId_2864_, lean_object* v_x_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1(v_00_u03b1_2863_, v_mvarId_2864_, v_x_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2879_) == 5)
{
lean_object* v_fn_2882_; lean_object* v_arg_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_fn_2882_ = lean_ctor_get(v_x_2879_, 0);
lean_inc_ref(v_fn_2882_);
v_arg_2883_ = lean_ctor_get(v_x_2879_, 1);
lean_inc_ref(v_arg_2883_);
lean_dec_ref_known(v_x_2879_, 2);
v___x_2884_ = lean_array_set(v_x_2880_, v_x_2881_, v_arg_2883_);
v___x_2885_ = lean_unsigned_to_nat(1u);
v___x_2886_ = lean_nat_sub(v_x_2881_, v___x_2885_);
lean_dec(v_x_2881_);
v_x_2879_ = v_fn_2882_;
v_x_2880_ = v___x_2884_;
v_x_2881_ = v___x_2886_;
goto _start;
}
else
{
lean_object* v___x_2888_; 
lean_dec(v_x_2881_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_x_2879_);
lean_ctor_set(v___x_2888_, 1, v_x_2880_);
return v___x_2888_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2894_; lean_object* v_dummy_2895_; 
v___x_2894_ = lean_box(0);
v_dummy_2895_ = l_Lean_Expr_sort___override(v___x_2894_);
return v_dummy_2895_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
return v___x_2912_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__10));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_r_2930_; lean_object* v___y_2931_; lean_object* v___y_2950_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_3021_; 
lean_inc(v_goal_2916_);
v___x_3021_ = l_Lean_MVarId_getType(v_goal_2916_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3247_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3247_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3247_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_options_3031_; lean_object* v_inheritedTraceOptions_3032_; uint8_t v_hasTrace_3033_; lean_object* v_cls_3034_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; 
v_options_3031_ = lean_ctor_get(v___y_2926_, 2);
v_inheritedTraceOptions_3032_ = lean_ctor_get(v___y_2926_, 13);
v_hasTrace_3033_ = lean_ctor_get_uint8(v_options_3031_, sizeof(void*)*1);
v_cls_3034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__6));
if (v_hasTrace_3033_ == 0)
{
v___y_3036_ = v___y_2917_;
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
goto v___jp_3035_;
}
else
{
lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_3234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3032_, v_options_3031_, v___x_3233_);
if (v___x_3234_ == 0)
{
v___y_3036_ = v___y_2917_;
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
goto v___jp_3035_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3235_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__11);
lean_inc(v_a_3022_);
v___x_3236_ = l_Lean_MessageData_ofExpr(v_a_3022_);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3034_, v___x_3237_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_dec_ref_known(v___x_3238_, 1);
v___y_3036_ = v___y_2917_;
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
goto v___jp_3035_;
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
v___jp_3026_:
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
v___jp_3035_:
{
lean_object* v___x_3047_; 
lean_inc(v_goal_2916_);
v___x_3047_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryForallIntro___redArg(v_goal_2916_, v_a_3022_, v___y_3036_, v___y_3037_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3224_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3224_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3224_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
if (lean_obj_tag(v_a_3048_) == 1)
{
lean_object* v_val_3052_; lean_object* v___x_3054_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_val_3052_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_val_3052_);
lean_dec_ref_known(v_a_3048_, 1);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_val_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_val_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
else
{
lean_object* v___x_3056_; 
lean_del_object(v___x_3050_);
lean_dec(v_a_3048_);
lean_inc(v_goal_2916_);
v___x_3056_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro(v_goal_2916_, v_a_3022_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3215_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3215_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3215_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
if (lean_obj_tag(v_a_3057_) == 1)
{
lean_object* v_val_3061_; lean_object* v___x_3063_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_val_3061_ = lean_ctor_get(v_a_3057_, 0);
lean_inc(v_val_3061_);
lean_dec_ref_known(v_a_3057_, 1);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v_val_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_val_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v___x_3065_; 
lean_del_object(v___x_3059_);
lean_dec(v_a_3057_);
lean_inc(v_goal_2916_);
v___x_3065_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTripleUnfold(v_goal_2916_, v_a_3022_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3206_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3206_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3206_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
if (lean_obj_tag(v_a_3066_) == 1)
{
lean_object* v_val_3070_; lean_object* v___x_3072_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_val_3070_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_val_3070_);
lean_dec_ref_known(v_a_3066_, 1);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v_val_3070_);
v___x_3072_ = v___x_3068_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_val_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
else
{
lean_object* v___x_3074_; 
lean_del_object(v___x_3068_);
lean_dec(v_a_3066_);
lean_inc(v_goal_2916_);
v___x_3074_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(v_goal_2916_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3197_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3197_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3197_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
if (lean_obj_tag(v_a_3075_) == 1)
{
lean_object* v_val_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_val_3079_ = lean_ctor_get(v_a_3075_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_3075_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3081_ = v_a_3075_;
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_val_3079_);
lean_dec(v_a_3075_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 4);
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_val_3079_);
v___x_3084_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3086_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3084_);
v___x_3086_ = v___x_3077_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
lean_del_object(v___x_3077_);
lean_dec(v_a_3075_);
lean_inc(v_a_3022_);
v___x_3090_ = l_Lean_Expr_cleanupAnnotations(v_a_3022_);
v___x_3091_ = l_Lean_Expr_isApp(v___x_3090_);
if (v___x_3091_ == 0)
{
lean_dec_ref(v___x_3090_);
lean_dec(v_goal_2916_);
goto v___jp_3026_;
}
else
{
lean_object* v_arg_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_arg_3092_ = lean_ctor_get(v___x_3090_, 1);
lean_inc_ref(v_arg_3092_);
v___x_3093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3090_);
v___x_3094_ = l_Lean_Expr_isApp(v___x_3093_);
if (v___x_3094_ == 0)
{
lean_dec_ref(v___x_3093_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
goto v___jp_3026_;
}
else
{
lean_object* v_arg_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_arg_3095_ = lean_ctor_get(v___x_3093_, 1);
lean_inc_ref(v_arg_3095_);
v___x_3096_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3093_);
v___x_3097_ = l_Lean_Expr_isApp(v___x_3096_);
if (v___x_3097_ == 0)
{
lean_dec_ref(v___x_3096_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
goto v___jp_3026_;
}
else
{
lean_object* v_arg_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_arg_3098_ = lean_ctor_get(v___x_3096_, 1);
lean_inc_ref(v_arg_3098_);
v___x_3099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3096_);
v___x_3100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
goto v___jp_3026_;
}
else
{
lean_object* v___x_3102_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_inc(v_goal_2916_);
v___x_3102_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryTargetLambdaIntro(v_goal_2916_, v_arg_3092_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3188_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3188_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3188_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
if (lean_obj_tag(v_a_3103_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3109_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
v_val_3107_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v_a_3103_, 1);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v_val_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_val_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3111_; 
lean_del_object(v___x_3105_);
lean_dec(v_a_3103_);
lean_inc_ref(v_arg_3092_);
lean_inc_ref(v_arg_3095_);
lean_inc_ref(v_arg_3098_);
lean_inc_ref(v___x_3099_);
lean_inc(v_goal_2916_);
v___x_3111_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryHeadReduceHT(v_goal_2916_, v___x_3099_, v_arg_3098_, v_arg_3095_, v_arg_3092_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3179_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3179_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3179_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
if (lean_obj_tag(v_a_3112_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3118_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
v_val_3116_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v_a_3112_, 1);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v_val_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_val_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
else
{
lean_object* v_dummy_3120_; lean_object* v_nargs_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_fst_3126_; lean_object* v_snd_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3178_; 
lean_del_object(v___x_3114_);
lean_dec(v_a_3112_);
v_dummy_3120_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v_nargs_3121_ = l_Lean_Expr_getAppNumArgs(v_arg_3092_);
lean_inc(v_nargs_3121_);
v___x_3122_ = lean_mk_array(v_nargs_3121_, v_dummy_3120_);
v___x_3123_ = lean_unsigned_to_nat(1u);
v___x_3124_ = lean_nat_sub(v_nargs_3121_, v___x_3123_);
lean_dec(v_nargs_3121_);
lean_inc_ref(v_arg_3092_);
v___x_3125_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__0(v_arg_3092_, v___x_3122_, v___x_3124_);
v_fst_3126_ = lean_ctor_get(v___x_3125_, 0);
v_snd_3127_ = lean_ctor_get(v___x_3125_, 1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3129_ = v___x_3125_;
v_isShared_3130_ = v_isSharedCheck_3178_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_snd_3127_);
lean_inc(v_fst_3126_);
lean_dec(v___x_3125_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3178_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_3132_ = l_Lean_Expr_isConstOf(v_fst_3126_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
v___x_3133_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryRflOrSPred(v_goal_2916_, v___x_3099_, v_arg_3098_, v_arg_3095_, v_arg_3092_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec_ref(v___x_3099_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3134_ = l_Lean_instInhabitedExpr;
v___x_3135_ = lean_unsigned_to_nat(2u);
v___x_3136_ = lean_array_get_borrowed(v___x_3134_, v_snd_3127_, v___x_3135_);
lean_inc(v___x_3136_);
v___x_3137_ = l_Lean_Expr_cleanupAnnotations(v___x_3136_);
v___x_3138_ = l_Lean_Expr_isApp(v___x_3137_);
if (v___x_3138_ == 0)
{
lean_dec_ref(v___x_3137_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_arg_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_arg_3139_ = lean_ctor_get(v___x_3137_, 1);
lean_inc_ref(v_arg_3139_);
v___x_3140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3137_);
v___x_3141_ = l_Lean_Expr_isApp(v___x_3140_);
if (v___x_3141_ == 0)
{
lean_dec_ref(v___x_3140_);
lean_dec_ref(v_arg_3139_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_arg_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_arg_3142_ = lean_ctor_get(v___x_3140_, 1);
lean_inc_ref(v_arg_3142_);
v___x_3143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3140_);
v___x_3144_ = l_Lean_Expr_isApp(v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec_ref(v___x_3143_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_arg_3139_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_arg_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_arg_3145_ = lean_ctor_get(v___x_3143_, 1);
lean_inc_ref(v_arg_3145_);
v___x_3146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3143_);
v___x_3147_ = l_Lean_Expr_isApp(v___x_3146_);
if (v___x_3147_ == 0)
{
lean_dec_ref(v___x_3146_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_arg_3139_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_arg_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_arg_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc_ref(v_arg_3148_);
v___x_3149_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3146_);
v___x_3150_ = l_Lean_Expr_isApp(v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec_ref(v___x_3149_);
lean_dec_ref(v_arg_3148_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_arg_3139_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_arg_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_arg_3151_ = lean_ctor_get(v___x_3149_, 1);
lean_inc_ref(v_arg_3151_);
v___x_3152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3149_);
v___x_3153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7));
v___x_3154_ = l_Lean_Expr_isConstOf(v___x_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_dec_ref(v___x_3152_);
lean_dec_ref(v_arg_3151_);
lean_dec_ref(v_arg_3148_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_arg_3139_);
lean_del_object(v___x_3129_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v___y_2950_ = v_arg_3092_;
goto v___jp_2949_;
}
else
{
lean_object* v_options_3155_; lean_object* v_inheritedTraceOptions_3156_; uint8_t v_hasTrace_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec_ref(v_arg_3092_);
v_options_3155_ = lean_ctor_get(v___y_3045_, 2);
v_inheritedTraceOptions_3156_ = lean_ctor_get(v___y_3045_, 13);
v_hasTrace_3157_ = lean_ctor_get_uint8(v_options_3155_, sizeof(void*)*1);
v___x_3158_ = lean_unsigned_to_nat(4u);
v___x_3159_ = lean_array_get_size(v_snd_3127_);
v___x_3160_ = l_Array_extract___redArg(v_snd_3127_, v___x_3158_, v___x_3159_);
v___x_3161_ = l_Lean_Expr_getAppFn(v_arg_3139_);
if (v_hasTrace_3157_ == 0)
{
lean_del_object(v___x_3129_);
v___y_2954_ = v___x_3152_;
v___y_2955_ = v___x_3161_;
v___y_2956_ = v_arg_3098_;
v___y_2957_ = v_arg_3148_;
v___y_2958_ = v___x_3099_;
v___y_2959_ = v_arg_3142_;
v___y_2960_ = v_arg_3139_;
v___y_2961_ = v_arg_3095_;
v___y_2962_ = v_fst_3126_;
v___y_2963_ = v___x_3160_;
v___y_2964_ = v_arg_3145_;
v___y_2965_ = v_snd_3127_;
v___y_2966_ = v_arg_3151_;
v___y_2967_ = v___y_3036_;
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
goto v___jp_2953_;
}
else
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro___closed__9);
v___x_3163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3156_, v_options_3155_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_del_object(v___x_3129_);
v___y_2954_ = v___x_3152_;
v___y_2955_ = v___x_3161_;
v___y_2956_ = v_arg_3098_;
v___y_2957_ = v_arg_3148_;
v___y_2958_ = v___x_3099_;
v___y_2959_ = v_arg_3142_;
v___y_2960_ = v_arg_3139_;
v___y_2961_ = v_arg_3095_;
v___y_2962_ = v_fst_3126_;
v___y_2963_ = v___x_3160_;
v___y_2964_ = v_arg_3145_;
v___y_2965_ = v_snd_3127_;
v___y_2966_ = v_arg_3151_;
v___y_2967_ = v___y_3036_;
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
goto v___jp_2953_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__9);
lean_inc_ref(v_arg_3139_);
v___x_3165_ = l_Lean_MessageData_ofExpr(v_arg_3139_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 7);
lean_ctor_set(v___x_3129_, 1, v___x_3165_);
lean_ctor_set(v___x_3129_, 0, v___x_3164_);
v___x_3167_ = v___x_3129_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetIntro_spec__0___redArg(v_cls_3034_, v___x_3167_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_dec_ref_known(v___x_3168_, 1);
v___y_2954_ = v___x_3152_;
v___y_2955_ = v___x_3161_;
v___y_2956_ = v_arg_3098_;
v___y_2957_ = v_arg_3148_;
v___y_2958_ = v___x_3099_;
v___y_2959_ = v_arg_3142_;
v___y_2960_ = v_arg_3139_;
v___y_2961_ = v_arg_3095_;
v___y_2962_ = v_fst_3126_;
v___y_2963_ = v___x_3160_;
v___y_2964_ = v_arg_3145_;
v___y_2965_ = v_snd_3127_;
v___y_2966_ = v_arg_3151_;
v___y_2967_ = v___y_3036_;
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
goto v___jp_2953_;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v___x_3161_);
lean_dec_ref(v___x_3160_);
lean_dec_ref(v___x_3152_);
lean_dec_ref(v_arg_3151_);
lean_dec_ref(v_arg_3148_);
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_arg_3139_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec(v_goal_2916_);
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
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
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
v_a_3180_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3111_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3111_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3098_);
lean_dec_ref(v_arg_3095_);
lean_dec_ref(v_arg_3092_);
lean_dec(v_goal_2916_);
v_a_3189_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3102_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3102_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
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
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_a_3198_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3074_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3074_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_a_3207_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3065_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3065_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_a_3216_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3056_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3056_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3024_);
lean_dec(v_a_3022_);
lean_dec(v_goal_2916_);
v_a_3225_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3047_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3047_);
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
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_goal_2916_);
v_a_3248_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3021_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3021_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
v___jp_2929_:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2932_, 0);
lean_dec(v_unused_2940_);
v___x_2934_ = v___x_2932_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v___x_2932_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v_r_2930_);
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_r_2930_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v_r_2930_);
v_a_2941_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2932_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2932_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
v___jp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___y_2950_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
v___jp_2953_:
{
lean_object* v___x_2978_; 
lean_inc_ref(v___y_2955_);
lean_inc_ref(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2956_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v___y_2962_);
lean_inc(v_goal_2916_);
v___x_2978_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryLetHoist(v_goal_2916_, v___y_2962_, v___y_2961_, v___y_2956_, v___y_2958_, v___y_2965_, v___y_2954_, v___y_2966_, v___y_2957_, v___y_2964_, v___y_2959_, v___y_2960_, v___y_2955_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
if (lean_obj_tag(v_a_2979_) == 1)
{
lean_object* v_val_2980_; 
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
lean_dec_ref(v___y_2954_);
lean_dec(v_goal_2916_);
v_val_2980_ = lean_ctor_get(v_a_2979_, 0);
lean_inc(v_val_2980_);
lean_dec_ref_known(v_a_2979_, 1);
v_r_2930_ = v_val_2980_;
v___y_2931_ = v___y_2968_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2981_; 
lean_dec(v_a_2979_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2965_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2956_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v___y_2962_);
lean_inc(v_goal_2916_);
v___x_2981_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_trySplit(v_goal_2916_, v___y_2962_, v___y_2961_, v___y_2956_, v___y_2958_, v___y_2965_, v___y_2954_, v___y_2966_, v___y_2957_, v___y_2964_, v___y_2959_, v___y_2960_, v___y_2963_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
if (lean_obj_tag(v_a_2982_) == 1)
{
lean_object* v_val_2983_; 
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
lean_dec_ref(v___y_2954_);
lean_dec(v_goal_2916_);
v_val_2983_ = lean_ctor_get(v_a_2982_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v_a_2982_, 1);
v_r_2930_ = v_val_2983_;
v___y_2931_ = v___y_2968_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2984_; 
lean_dec(v_a_2982_);
lean_inc_ref(v___y_2960_);
lean_inc_ref(v___y_2964_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2956_);
lean_inc(v_goal_2916_);
v___x_2984_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryFvarZeta(v_goal_2916_, v___y_2962_, v___y_2961_, v___y_2956_, v___y_2958_, v___y_2965_, v___y_2954_, v___y_2966_, v___y_2957_, v___y_2964_, v___y_2959_, v___y_2960_, v___y_2955_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v___y_2955_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
if (lean_obj_tag(v_a_2985_) == 1)
{
lean_object* v_val_2986_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2916_);
v_val_2986_ = lean_ctor_get(v_a_2985_, 0);
lean_inc(v_val_2986_);
lean_dec_ref_known(v_a_2985_, 1);
v_r_2930_ = v_val_2986_;
v___y_2931_ = v___y_2968_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_a_2985_);
v___x_2987_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_2968_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v___x_2988_; 
lean_dec_ref_known(v___x_2987_, 1);
v___x_2988_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_goal_2916_, v___y_2960_, v___y_2963_, v___y_2966_, v___y_2956_, v___y_2957_, v___y_2964_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_2988_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2916_);
v_a_2989_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2987_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_goal_2916_);
v_a_2997_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2984_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2984_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
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
lean_dec_ref(v___y_2954_);
lean_dec(v_goal_2916_);
v_a_3005_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2981_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2981_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
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
lean_dec_ref(v___y_2954_);
lean_dec(v_goal_2916_);
v_a_3013_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2978_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2978_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_goal_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v___f_3283_; lean_object* v___x_3284_; 
lean_inc(v_goal_3270_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3283_, 0, v_goal_3270_);
v___x_3284_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solve_spec__1___redArg(v_goal_3270_, v___f_3283_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_goal_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_goal_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
return v_res_3298_;
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
