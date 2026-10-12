// Lean compiler output
// Module: Lean.Meta.Sym.Grind
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Tactic.Grind.Main import Lean.Meta.Sym.Simp.Goal import Lean.Meta.Sym.Intro import Lean.Meta.Sym.Util import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Tactic.Grind.Solve import Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIssues___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalizeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_grind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_grind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_assumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoal(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v___x_12_, 1);
v___x_14_ = l_Lean_Meta_Grind_mkGoalCore(v_a_13_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_22_; 
v_a_15_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_22_ == 0)
{
v___x_17_ = v___x_12_;
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_a_15_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_Meta_Grind_mkGoal(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal___boxed(lean_object* v_mvarId_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Grind_mkGoal(v_mvarId_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___impl(lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_tag_nat(v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___impl___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Grind_IntrosResult_ctorIdx___impl(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(lean_object* v_t_40_, lean_object* v_k_41_){
_start:
{
if (lean_obj_tag(v_t_40_) == 0)
{
return v_k_41_;
}
else
{
lean_object* v_newDecls_42_; lean_object* v_goal_43_; lean_object* v___x_44_; 
v_newDecls_42_ = lean_ctor_get(v_t_40_, 0);
lean_inc_ref(v_newDecls_42_);
v_goal_43_ = lean_ctor_get(v_t_40_, 1);
lean_inc_ref(v_goal_43_);
lean_dec_ref_known(v_t_40_, 2);
v___x_44_ = lean_apply_2(v_k_41_, v_newDecls_42_, v_goal_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim(lean_object* v_motive_45_, lean_object* v_ctorIdx_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_k_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_47_, v_k_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___boxed(lean_object* v_motive_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_Grind_IntrosResult_ctorElim(v_motive_51_, v_ctorIdx_52_, v_t_53_, v_h_54_, v_k_55_);
lean_dec(v_ctorIdx_52_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim___redArg(lean_object* v_t_57_, lean_object* v_failed_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_57_, v_failed_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_failed_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_61_, v_failed_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim___redArg(lean_object* v_t_65_, lean_object* v_goal_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_65_, v_goal_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_goal_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(v_t_69_, v_goal_71_);
return v___x_72_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_introN(lean_object* v_goal_73_, lean_object* v_num_74_, uint8_t v_hygienic_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_toGoalState_83_; lean_object* v_mvarId_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_121_; 
v_toGoalState_83_ = lean_ctor_get(v_goal_73_, 0);
v_mvarId_84_ = lean_ctor_get(v_goal_73_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_goal_73_);
if (v_isSharedCheck_121_ == 0)
{
v___x_86_ = v_goal_73_;
v_isShared_87_ = v_isSharedCheck_121_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_mvarId_84_);
lean_inc(v_toGoalState_83_);
lean_dec(v_goal_73_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_121_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_Sym_introN(v_mvarId_84_, v_num_74_, v_hygienic_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_112_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_112_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_112_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_112_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
if (lean_obj_tag(v_a_89_) == 1)
{
lean_object* v_newDecls_93_; lean_object* v_mvarId_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_107_; 
v_newDecls_93_ = lean_ctor_get(v_a_89_, 0);
v_mvarId_94_ = lean_ctor_get(v_a_89_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_a_89_);
if (v_isSharedCheck_107_ == 0)
{
v___x_96_ = v_a_89_;
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_mvarId_94_);
lean_inc(v_newDecls_93_);
lean_dec(v_a_89_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_mvarId_94_);
v___x_99_ = v___x_86_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_toGoalState_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_mvarId_94_);
v___x_99_ = v_reuseFailAlloc_106_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_99_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_newDecls_93_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_105_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_103_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_101_);
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
else
{
lean_object* v___x_108_; lean_object* v___x_110_; 
lean_dec(v_a_89_);
lean_del_object(v___x_86_);
lean_dec_ref(v_toGoalState_83_);
v___x_108_ = lean_box(0);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_108_);
v___x_110_ = v___x_91_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_del_object(v___x_86_);
lean_dec_ref(v_toGoalState_83_);
v_a_113_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_88_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_88_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_introN_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_73_ = stack[0].m_obj;
lean_object* v_num_74_ = stack[1].m_obj;
uint8_t v_hygienic_75_ = stack[2].m_num;
lean_object* v_a_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_a_78_ = stack[5].m_obj;
lean_object* v_a_79_ = stack[6].m_obj;
lean_object* v_a_80_ = stack[7].m_obj;
lean_object* v_a_81_ = stack[8].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Meta_Grind_Goal_introN(v_goal_73_, v_num_74_, v_hygienic_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object* v_goal_123_, lean_object* v_num_124_, lean_object* v_hygienic_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
uint8_t v_hygienic_boxed_133_; lean_object* v_res_134_; 
v_hygienic_boxed_133_ = lean_unbox(v_hygienic_125_);
v_res_134_ = l_Lean_Meta_Grind_Goal_introN(v_goal_123_, v_num_124_, v_hygienic_boxed_133_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_134_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_intros(lean_object* v_goal_135_, lean_object* v_names_136_, uint8_t v_hygienic_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_toGoalState_145_; lean_object* v_mvarId_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_183_; 
v_toGoalState_145_ = lean_ctor_get(v_goal_135_, 0);
v_mvarId_146_ = lean_ctor_get(v_goal_135_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_goal_135_);
if (v_isSharedCheck_183_ == 0)
{
v___x_148_ = v_goal_135_;
v_isShared_149_ = v_isSharedCheck_183_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_mvarId_146_);
lean_inc(v_toGoalState_145_);
lean_dec(v_goal_135_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_183_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Sym_intros(v_mvarId_146_, v_names_136_, v_hygienic_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_174_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_174_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_174_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_174_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
if (lean_obj_tag(v_a_151_) == 1)
{
lean_object* v_newDecls_155_; lean_object* v_mvarId_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_169_; 
v_newDecls_155_ = lean_ctor_get(v_a_151_, 0);
v_mvarId_156_ = lean_ctor_get(v_a_151_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_a_151_);
if (v_isSharedCheck_169_ == 0)
{
v___x_158_ = v_a_151_;
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_mvarId_156_);
lean_inc(v_newDecls_155_);
lean_dec(v_a_151_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_169_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_mvarId_156_);
v___x_161_ = v___x_148_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_toGoalState_145_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_mvarId_156_);
v___x_161_ = v_reuseFailAlloc_168_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_newDecls_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_167_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_163_);
v___x_165_ = v___x_153_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_172_; 
lean_dec(v_a_151_);
lean_del_object(v___x_148_);
lean_dec_ref(v_toGoalState_145_);
v___x_170_ = lean_box(0);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_170_);
v___x_172_ = v___x_153_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_del_object(v___x_148_);
lean_dec_ref(v_toGoalState_145_);
v_a_175_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_150_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_150_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_intros_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_135_ = stack[0].m_obj;
lean_object* v_names_136_ = stack[1].m_obj;
uint8_t v_hygienic_137_ = stack[2].m_num;
lean_object* v_a_138_ = stack[3].m_obj;
lean_object* v_a_139_ = stack[4].m_obj;
lean_object* v_a_140_ = stack[5].m_obj;
lean_object* v_a_141_ = stack[6].m_obj;
lean_object* v_a_142_ = stack[7].m_obj;
lean_object* v_a_143_ = stack[8].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Meta_Grind_Goal_intros(v_goal_135_, v_names_136_, v_hygienic_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object* v_goal_185_, lean_object* v_names_186_, lean_object* v_hygienic_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
uint8_t v_hygienic_boxed_195_; lean_object* v_res_196_; 
v_hygienic_boxed_195_ = lean_unbox(v_hygienic_187_);
v_res_196_ = l_Lean_Meta_Grind_Goal_intros(v_goal_185_, v_names_186_, v_hygienic_boxed_195_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___impl(lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_tag_nat(v_x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___impl___boxed(lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_Grind_ApplyResult_ctorIdx___impl(v_x_199_);
lean_dec(v_x_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(lean_object* v_t_201_, lean_object* v_k_202_){
_start:
{
if (lean_obj_tag(v_t_201_) == 0)
{
return v_k_202_;
}
else
{
lean_object* v_subgoals_203_; lean_object* v___x_204_; 
v_subgoals_203_ = lean_ctor_get(v_t_201_, 0);
lean_inc(v_subgoals_203_);
lean_dec_ref_known(v_t_201_, 1);
v___x_204_ = lean_apply_1(v_k_202_, v_subgoals_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_207_, v_k_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___boxed(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_Grind_ApplyResult_ctorElim(v_motive_211_, v_ctorIdx_212_, v_t_213_, v_h_214_, v_k_215_);
lean_dec(v_ctorIdx_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim___redArg(lean_object* v_t_217_, lean_object* v_failed_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_217_, v_failed_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim(lean_object* v_motive_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_failed_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_221_, v_failed_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim___redArg(lean_object* v_t_225_, lean_object* v_goals_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_225_, v_goals_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_goals_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_229_, v_goals_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(lean_object* v_goal_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
if (lean_obj_tag(v_a_234_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = l_List_reverse___redArg(v_a_235_);
return v___x_236_;
}
else
{
lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_248_; 
v_head_237_ = lean_ctor_get(v_a_234_, 0);
v_tail_238_ = lean_ctor_get(v_a_234_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_234_);
if (v_isSharedCheck_248_ == 0)
{
v___x_240_ = v_a_234_;
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_tail_238_);
lean_inc(v_head_237_);
lean_dec(v_a_234_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_toGoalState_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v_toGoalState_242_ = lean_ctor_get(v_goal_233_, 0);
lean_inc_ref(v_toGoalState_242_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_toGoalState_242_);
lean_ctor_set(v___x_243_, 1, v_head_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_a_235_);
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_a_235_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v_a_234_ = v_tail_238_;
v_a_235_ = v___x_245_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0___boxed(lean_object* v_goal_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(v_goal_249_, v_a_250_, v_a_251_);
lean_dec_ref(v_goal_249_);
return v_res_252_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_apply(lean_object* v_goal_253_, lean_object* v_rule_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_mvarId_262_; lean_object* v___x_263_; 
v_mvarId_262_ = lean_ctor_get(v_goal_253_, 1);
lean_inc(v_mvarId_262_);
v___x_263_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_262_, v_rule_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_285_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_285_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_285_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_285_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
if (lean_obj_tag(v_a_264_) == 1)
{
lean_object* v_mvarIds_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
v_mvarIds_268_ = lean_ctor_get(v_a_264_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_280_ == 0)
{
v___x_270_ = v_a_264_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_mvarIds_268_);
lean_dec(v_a_264_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
v___x_273_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(v_goal_253_, v_mvarIds_268_, v___x_272_);
lean_dec_ref(v_goal_253_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_275_);
v___x_277_ = v___x_266_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec(v_a_264_);
lean_dec_ref(v_goal_253_);
v___x_281_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_281_);
v___x_283_ = v___x_266_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_goal_253_);
v_a_286_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_263_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_263_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_apply_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_253_ = stack[0].m_obj;
lean_object* v_rule_254_ = stack[1].m_obj;
lean_object* v_a_255_ = stack[2].m_obj;
lean_object* v_a_256_ = stack[3].m_obj;
lean_object* v_a_257_ = stack[4].m_obj;
lean_object* v_a_258_ = stack[5].m_obj;
lean_object* v_a_259_ = stack[6].m_obj;
lean_object* v_a_260_ = stack[7].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_Grind_Goal_apply(v_goal_253_, v_rule_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_apply___boxed(lean_object* v_goal_295_, lean_object* v_rule_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Goal_apply(v_goal_295_, v_rule_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___impl(lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_tag_nat(v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___impl___boxed(lean_object* v_x_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___impl(v_x_307_);
lean_dec(v_x_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(lean_object* v_t_309_, lean_object* v_k_310_){
_start:
{
if (lean_obj_tag(v_t_309_) == 2)
{
lean_object* v_goal_311_; lean_object* v___x_312_; 
v_goal_311_ = lean_ctor_get(v_t_309_, 0);
lean_inc_ref(v_goal_311_);
lean_dec_ref_known(v_t_309_, 1);
v___x_312_ = lean_apply_1(v_k_310_, v_goal_311_);
return v___x_312_;
}
else
{
lean_dec(v_t_309_);
return v_k_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_k_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_315_, v_k_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___boxed(lean_object* v_motive_319_, lean_object* v_ctorIdx_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim(v_motive_319_, v_ctorIdx_320_, v_t_321_, v_h_322_, v_k_323_);
lean_dec(v_ctorIdx_320_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim___redArg(lean_object* v_t_325_, lean_object* v_noProgress_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_325_, v_noProgress_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim(lean_object* v_motive_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_noProgress_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_329_, v_noProgress_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim___redArg(lean_object* v_t_333_, lean_object* v_closed_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_333_, v_closed_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim(lean_object* v_motive_336_, lean_object* v_t_337_, lean_object* v_h_338_, lean_object* v_closed_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_337_, v_closed_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim___redArg(lean_object* v_t_341_, lean_object* v_goal_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_341_, v_goal_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_goal_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_345_, v_goal_347_);
return v___x_348_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_simp(lean_object* v_goal_349_, lean_object* v_methods_350_, lean_object* v_config_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_toGoalState_359_; lean_object* v_mvarId_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_400_; 
v_toGoalState_359_ = lean_ctor_get(v_goal_349_, 0);
v_mvarId_360_ = lean_ctor_get(v_goal_349_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_goal_349_);
if (v_isSharedCheck_400_ == 0)
{
v___x_362_ = v_goal_349_;
v_isShared_363_ = v_isSharedCheck_400_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_mvarId_360_);
lean_inc(v_toGoalState_359_);
lean_dec(v_goal_349_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_400_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_360_, v_methods_350_, v_config_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_391_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_391_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_391_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_391_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
switch(lean_obj_tag(v_a_365_))
{
case 0:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_del_object(v___x_362_);
lean_dec_ref(v_toGoalState_359_);
v___x_369_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
case 1:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
lean_del_object(v___x_362_);
lean_dec_ref(v_toGoalState_359_);
v___x_373_ = lean_box(1);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_373_);
v___x_375_ = v___x_367_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
default: 
{
lean_object* v_mvarId_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_390_; 
v_mvarId_377_ = lean_ctor_get(v_a_365_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_390_ == 0)
{
v___x_379_ = v_a_365_;
v_isShared_380_ = v_isSharedCheck_390_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_mvarId_377_);
lean_dec(v_a_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_390_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_mvarId_377_);
v___x_382_ = v___x_362_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_toGoalState_359_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_mvarId_377_);
v___x_382_ = v_reuseFailAlloc_389_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_382_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_384_);
v___x_386_ = v___x_367_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
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
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_del_object(v___x_362_);
lean_dec_ref(v_toGoalState_359_);
v_a_392_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_364_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_364_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_349_ = stack[0].m_obj;
lean_object* v_methods_350_ = stack[1].m_obj;
lean_object* v_config_351_ = stack[2].m_obj;
lean_object* v_a_352_ = stack[3].m_obj;
lean_object* v_a_353_ = stack[4].m_obj;
lean_object* v_a_354_ = stack[5].m_obj;
lean_object* v_a_355_ = stack[6].m_obj;
lean_object* v_a_356_ = stack[7].m_obj;
lean_object* v_a_357_ = stack[8].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_Meta_Grind_Goal_simp(v_goal_349_, v_methods_350_, v_config_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simp___boxed(lean_object* v_goal_402_, lean_object* v_methods_403_, lean_object* v_config_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Goal_simp(v_goal_402_, v_methods_403_, v_config_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_412_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(lean_object* v_goal_413_, lean_object* v_methods_414_, lean_object* v_config_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_toGoalState_423_; lean_object* v_mvarId_424_; lean_object* v___x_425_; 
v_toGoalState_423_ = lean_ctor_get(v_goal_413_, 0);
v_mvarId_424_ = lean_ctor_get(v_goal_413_, 1);
lean_inc(v_mvarId_424_);
v___x_425_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_424_, v_methods_414_, v_config_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_458_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_458_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_458_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_458_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
switch(lean_obj_tag(v_a_426_))
{
case 0:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_430_, 0, v_goal_413_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
case 1:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec_ref(v_goal_413_);
v___x_434_ = lean_box(1);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_434_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
default: 
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_455_; 
lean_inc_ref(v_toGoalState_423_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_goal_413_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; 
v_unused_456_ = lean_ctor_get(v_goal_413_, 1);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_goal_413_, 0);
lean_dec(v_unused_457_);
v___x_439_ = v_goal_413_;
v_isShared_440_ = v_isSharedCheck_455_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_goal_413_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_455_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_mvarId_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_454_; 
v_mvarId_441_ = lean_ctor_get(v_a_426_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_454_ == 0)
{
v___x_443_ = v_a_426_;
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_mvarId_441_);
lean_dec(v_a_426_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_mvarId_441_);
v___x_446_ = v___x_439_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_toGoalState_423_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_mvarId_441_);
v___x_446_ = v_reuseFailAlloc_453_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_448_);
v___x_450_ = v___x_428_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
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
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_goal_413_);
v_a_459_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_425_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_425_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_413_ = stack[0].m_obj;
lean_object* v_methods_414_ = stack[1].m_obj;
lean_object* v_config_415_ = stack[2].m_obj;
lean_object* v_a_416_ = stack[3].m_obj;
lean_object* v_a_417_ = stack[4].m_obj;
lean_object* v_a_418_ = stack[5].m_obj;
lean_object* v_a_419_ = stack[6].m_obj;
lean_object* v_a_420_ = stack[7].m_obj;
lean_object* v_a_421_ = stack[8].m_obj;
lean_object* v_res_467_;
v_res_467_ = l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(v_goal_413_, v_methods_414_, v_config_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress___boxed(lean_object* v_goal_468_, lean_object* v_methods_469_, lean_object* v_config_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(v_goal_468_, v_methods_469_, v_config_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_478_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_internalize(lean_object* v_goal_479_, lean_object* v_num_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_num_480_);
v___x_492_ = l_Lean_Meta_Grind_processHypotheses(v_goal_479_, v___x_491_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v___x_492_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_internalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_479_ = stack[0].m_obj;
lean_object* v_num_480_ = stack[1].m_obj;
lean_object* v_a_481_ = stack[2].m_obj;
lean_object* v_a_482_ = stack[3].m_obj;
lean_object* v_a_483_ = stack[4].m_obj;
lean_object* v_a_484_ = stack[5].m_obj;
lean_object* v_a_485_ = stack[6].m_obj;
lean_object* v_a_486_ = stack[7].m_obj;
lean_object* v_a_487_ = stack[8].m_obj;
lean_object* v_a_488_ = stack[9].m_obj;
lean_object* v_a_489_ = stack[10].m_obj;
lean_object* v_res_493_;
v_res_493_ = l_Lean_Meta_Grind_Goal_internalize(v_goal_479_, v_num_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalize___boxed(lean_object* v_goal_494_, lean_object* v_num_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Grind_Goal_internalize(v_goal_494_, v_num_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
return v_res_506_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_internalizeAll(lean_object* v_goal_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = l_Lean_Meta_Grind_processHypotheses(v_goal_507_, v___x_518_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_519_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_internalizeAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_507_ = stack[0].m_obj;
lean_object* v_a_508_ = stack[1].m_obj;
lean_object* v_a_509_ = stack[2].m_obj;
lean_object* v_a_510_ = stack[3].m_obj;
lean_object* v_a_511_ = stack[4].m_obj;
lean_object* v_a_512_ = stack[5].m_obj;
lean_object* v_a_513_ = stack[6].m_obj;
lean_object* v_a_514_ = stack[7].m_obj;
lean_object* v_a_515_ = stack[8].m_obj;
lean_object* v_a_516_ = stack[9].m_obj;
lean_object* v_res_520_;
v_res_520_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object* v_goal_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___impl(lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_tag_nat(v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___impl___boxed(lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Grind_GrindResult_ctorIdx___impl(v_x_535_);
lean_dec(v_x_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(lean_object* v_t_537_, lean_object* v_k_538_){
_start:
{
if (lean_obj_tag(v_t_537_) == 0)
{
lean_object* v_goal_539_; lean_object* v___x_540_; 
v_goal_539_ = lean_ctor_get(v_t_537_, 0);
lean_inc_ref(v_goal_539_);
lean_dec_ref_known(v_t_537_, 1);
v___x_540_ = lean_apply_1(v_k_538_, v_goal_539_);
return v___x_540_;
}
else
{
return v_k_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim(lean_object* v_motive_541_, lean_object* v_ctorIdx_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_k_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_543_, v_k_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___boxed(lean_object* v_motive_547_, lean_object* v_ctorIdx_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_k_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Grind_GrindResult_ctorElim(v_motive_547_, v_ctorIdx_548_, v_t_549_, v_h_550_, v_k_551_);
lean_dec(v_ctorIdx_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim___redArg(lean_object* v_t_553_, lean_object* v_failed_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_553_, v_failed_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim(lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_failed_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_557_, v_failed_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim___redArg(lean_object* v_t_561_, lean_object* v_closed_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_561_, v_closed_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_closed_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_565_, v_closed_567_);
return v___x_568_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_grind(lean_object* v_goal_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_Grind_solve(v_goal_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_600_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_600_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_600_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_600_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
if (lean_obj_tag(v_a_581_) == 1)
{
lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_595_; 
v_val_585_ = lean_ctor_get(v_a_581_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_595_ == 0)
{
v___x_587_ = v_a_581_;
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_dec(v_a_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 0);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_585_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_590_);
v___x_592_ = v___x_583_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v_a_581_);
v___x_596_ = lean_box(1);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_596_);
v___x_598_ = v___x_583_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_a_601_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_580_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_580_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_grind_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_569_ = stack[0].m_obj;
lean_object* v_a_570_ = stack[1].m_obj;
lean_object* v_a_571_ = stack[2].m_obj;
lean_object* v_a_572_ = stack[3].m_obj;
lean_object* v_a_573_ = stack[4].m_obj;
lean_object* v_a_574_ = stack[5].m_obj;
lean_object* v_a_575_ = stack[6].m_obj;
lean_object* v_a_576_ = stack[7].m_obj;
lean_object* v_a_577_ = stack[8].m_obj;
lean_object* v_a_578_ = stack[9].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_Lean_Meta_Grind_Goal_grind(v_goal_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_grind___boxed(lean_object* v_goal_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Meta_Grind_Goal_grind(v_goal_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
return v_res_621_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_assumption(lean_object* v_goal_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_mvarId_628_; lean_object* v___x_629_; 
v_mvarId_628_ = lean_ctor_get(v_goal_622_, 1);
lean_inc(v_mvarId_628_);
lean_dec_ref(v_goal_622_);
v___x_629_ = l_Lean_MVarId_assumptionCore(v_mvarId_628_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_assumption_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_622_ = stack[0].m_obj;
lean_object* v_a_623_ = stack[1].m_obj;
lean_object* v_a_624_ = stack[2].m_obj;
lean_object* v_a_625_ = stack[3].m_obj;
lean_object* v_a_626_ = stack[4].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Meta_Grind_Goal_assumption(v_goal_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_assumption___boxed(lean_object* v_goal_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Meta_Grind_Goal_assumption(v_goal_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_637_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(lean_object* v_e_638_, lean_object* v___y_639_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_hasMVar(v_e_638_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_e_638_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v_mctx_644_; lean_object* v___x_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v___x_648_; lean_object* v_cache_649_; lean_object* v_zetaDeltaFVarIds_650_; lean_object* v_postponed_651_; lean_object* v_diag_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v___x_643_ = lean_st_ref_get(v___y_639_);
v_mctx_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_mctx_644_);
lean_dec(v___x_643_);
v___x_645_ = l_Lean_instantiateMVarsCore(v_mctx_644_, v_e_638_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
v_snd_647_ = lean_ctor_get(v___x_645_, 1);
lean_inc(v_snd_647_);
lean_dec_ref(v___x_645_);
v___x_648_ = lean_st_ref_take(v___y_639_);
v_cache_649_ = lean_ctor_get(v___x_648_, 1);
v_zetaDeltaFVarIds_650_ = lean_ctor_get(v___x_648_, 2);
v_postponed_651_ = lean_ctor_get(v___x_648_, 3);
v_diag_652_ = lean_ctor_get(v___x_648_, 4);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_648_, 0);
lean_dec(v_unused_662_);
v___x_654_ = v___x_648_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_diag_652_);
lean_inc(v_postponed_651_);
lean_inc(v_zetaDeltaFVarIds_650_);
lean_inc(v_cache_649_);
lean_dec(v___x_648_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_snd_647_);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_snd_647_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_cache_649_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_zetaDeltaFVarIds_650_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_postponed_651_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v_diag_652_);
v___x_657_ = v_reuseFailAlloc_660_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_st_ref_put(v___y_639_, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_fst_646_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_638_ = stack[0].m_obj;
lean_object* v___y_639_ = stack[1].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(v_e_638_, v___y_639_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg___boxed(lean_object* v_e_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(v_e_664_, v___y_665_);
lean_dec(v___y_665_);
return v_res_667_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0(lean_object* v_e_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(v_e_668_, v___y_675_);
return v___x_679_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_668_ = stack[0].m_obj;
lean_object* v___y_669_ = stack[1].m_obj;
lean_object* v___y_670_ = stack[2].m_obj;
lean_object* v___y_671_ = stack[3].m_obj;
lean_object* v___y_672_ = stack[4].m_obj;
lean_object* v___y_673_ = stack[5].m_obj;
lean_object* v___y_674_ = stack[6].m_obj;
lean_object* v___y_675_ = stack[7].m_obj;
lean_object* v___y_676_ = stack[8].m_obj;
lean_object* v___y_677_ = stack[9].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0(v_e_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___boxed(lean_object* v_e_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0(v_e_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
return v_res_692_;
}
}
lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_x3f_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_share_698_; lean_object* v_maxFVar_699_; lean_object* v_proofInstInfo_700_; lean_object* v_proofInstInfoFVar_701_; lean_object* v_inferType_702_; lean_object* v_getLevel_703_; lean_object* v_congrInfo_704_; lean_object* v_defEqI_705_; lean_object* v_extensions_706_; lean_object* v_canon_707_; lean_object* v_instanceOverrides_708_; uint8_t v_debug_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_719_; 
v___x_697_ = lean_st_ref_take(v_a_693_);
v_share_698_ = lean_ctor_get(v___x_697_, 0);
v_maxFVar_699_ = lean_ctor_get(v___x_697_, 1);
v_proofInstInfo_700_ = lean_ctor_get(v___x_697_, 2);
v_proofInstInfoFVar_701_ = lean_ctor_get(v___x_697_, 3);
v_inferType_702_ = lean_ctor_get(v___x_697_, 4);
v_getLevel_703_ = lean_ctor_get(v___x_697_, 5);
v_congrInfo_704_ = lean_ctor_get(v___x_697_, 6);
v_defEqI_705_ = lean_ctor_get(v___x_697_, 7);
v_extensions_706_ = lean_ctor_get(v___x_697_, 8);
v_canon_707_ = lean_ctor_get(v___x_697_, 10);
v_instanceOverrides_708_ = lean_ctor_get(v___x_697_, 11);
v_debug_709_ = lean_ctor_get_uint8(v___x_697_, sizeof(void*)*12);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_697_, 9);
lean_dec(v_unused_720_);
v___x_711_ = v___x_697_;
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_instanceOverrides_708_);
lean_inc(v_canon_707_);
lean_inc(v_extensions_706_);
lean_inc(v_defEqI_705_);
lean_inc(v_congrInfo_704_);
lean_inc(v_getLevel_703_);
lean_inc(v_inferType_702_);
lean_inc(v_proofInstInfoFVar_701_);
lean_inc(v_proofInstInfo_700_);
lean_inc(v_maxFVar_699_);
lean_inc(v_share_698_);
lean_dec(v___x_697_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 9, v_a_694_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_share_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_maxFVar_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_proofInstInfo_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_proofInstInfoFVar_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_inferType_702_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_getLevel_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_congrInfo_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_defEqI_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_extensions_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v_a_694_);
lean_ctor_set(v_reuseFailAlloc_718_, 10, v_canon_707_);
lean_ctor_set(v_reuseFailAlloc_718_, 11, v_instanceOverrides_708_);
lean_ctor_set_uint8(v_reuseFailAlloc_718_, sizeof(void*)*12, v_debug_709_);
v___x_715_ = v_reuseFailAlloc_718_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_st_ref_put(v_a_693_, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_713_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_693_ = stack[0].m_obj;
lean_object* v_a_694_ = stack[1].m_obj;
lean_object* v_a_x3f_695_ = stack[2].m_obj;
lean_object* v_res_721_;
v_res_721_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(v_a_693_, v_a_694_, v_a_x3f_695_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0___boxed(lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_x3f_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(v_a_722_, v_a_723_, v_a_x3f_724_);
lean_dec(v_a_x3f_724_);
lean_dec(v_a_722_);
return v_res_726_;
}
}
lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp(lean_object* v_goal_731_, lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Sym_instantiateMVarsS(v_e_732_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_737_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_748_; lean_object* v_a_760_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_772_ = lean_box(0);
v___x_773_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_744_, v___x_772_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_toGoalState_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_802_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v_toGoalState_775_ = lean_ctor_get(v_goal_731_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_goal_731_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_goal_731_, 1);
lean_dec(v_unused_803_);
v___x_777_ = v_goal_731_;
v_isShared_778_ = v_isSharedCheck_802_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_toGoalState_775_);
lean_dec(v_goal_731_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_802_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_Expr_mvarId_x21(v_a_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_toGoalState_775_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_801_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_box(0);
v___x_783_ = l_Lean_Meta_Grind_processHypotheses(v___x_781_, v___x_782_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = l_Lean_Meta_Grind_solve(v_a_784_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
if (lean_obj_tag(v_a_786_) == 0)
{
uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v___x_787_ = 1;
v___x_788_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_spec__0___redArg(v_a_774_, v_a_739_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_793_, 0, v_a_789_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*1, v___x_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v_a_760_ = v___x_795_;
goto v___jp_759_;
}
}
}
else
{
lean_object* v___x_798_; 
lean_dec_ref_known(v_a_786_, 1);
lean_dec(v_a_774_);
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___closed__1));
v_a_760_ = v___x_798_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_799_; 
lean_dec(v_a_774_);
v_a_799_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_785_, 1);
v_a_748_ = v_a_799_;
goto v___jp_747_;
}
}
else
{
lean_object* v_a_800_; 
lean_dec(v_a_774_);
v_a_800_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_783_, 1);
v_a_748_ = v_a_800_;
goto v___jp_747_;
}
}
}
}
else
{
lean_object* v_a_804_; 
lean_dec_ref(v_goal_731_);
v_a_804_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_773_, 1);
v_a_748_ = v_a_804_;
goto v___jp_747_;
}
v___jp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v___x_749_ = lean_box(0);
v___x_750_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(v_a_737_, v_a_746_, v___x_749_);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_758_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v_a_748_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_748_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
lean_inc_ref(v_a_760_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_a_760_);
v___x_762_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___lam__0(v_a_737_, v_a_746_, v___x_761_);
lean_dec_ref_known(v___x_761_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v___x_762_, 0);
lean_dec(v_unused_771_);
v___x_764_ = v___x_762_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_a_766_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v_a_760_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v_a_760_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_a_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_a_744_);
lean_dec_ref(v_goal_731_);
v_a_805_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_745_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_745_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_goal_731_);
v_a_813_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_743_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_743_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_731_ = stack[0].m_obj;
lean_object* v_e_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_a_734_ = stack[3].m_obj;
lean_object* v_a_735_ = stack[4].m_obj;
lean_object* v_a_736_ = stack[5].m_obj;
lean_object* v_a_737_ = stack[6].m_obj;
lean_object* v_a_738_ = stack[7].m_obj;
lean_object* v_a_739_ = stack[8].m_obj;
lean_object* v_a_740_ = stack[9].m_obj;
lean_object* v_a_741_ = stack[10].m_obj;
lean_object* v_res_821_;
v_res_821_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp(v_goal_731_, v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp___boxed(lean_object* v_goal_822_, lean_object* v_e_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp(v_goal_822_, v_e_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
return v_res_834_;
}
}
lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg(lean_object* v_goal_835_, lean_object* v_methods_836_, lean_object* v_ctx_837_, lean_object* v_s_838_, lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_st_mk_ref(v_s_838_);
v___x_848_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_Goal_dischargeSymSimp(v_goal_835_, v_e_839_, v_methods_836_, v_ctx_837_, v___x_847_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_st_ref_get(v___x_847_);
lean_dec(v___x_847_);
lean_dec(v___x_853_);
if (v_isShared_852_ == 0)
{
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_849_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_dec(v___x_847_);
return v___x_848_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_835_ = stack[0].m_obj;
lean_object* v_methods_836_ = stack[1].m_obj;
lean_object* v_ctx_837_ = stack[2].m_obj;
lean_object* v_s_838_ = stack[3].m_obj;
lean_object* v_e_839_ = stack[4].m_obj;
lean_object* v_a_840_ = stack[5].m_obj;
lean_object* v_a_841_ = stack[6].m_obj;
lean_object* v_a_842_ = stack[7].m_obj;
lean_object* v_a_843_ = stack[8].m_obj;
lean_object* v_a_844_ = stack[9].m_obj;
lean_object* v_a_845_ = stack[10].m_obj;
lean_object* v_res_858_;
v_res_858_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg(v_goal_835_, v_methods_836_, v_ctx_837_, v_s_838_, v_e_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg___boxed(lean_object* v_goal_859_, lean_object* v_methods_860_, lean_object* v_ctx_861_, lean_object* v_s_862_, lean_object* v_e_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg(v_goal_859_, v_methods_860_, v_ctx_861_, v_s_862_, v_e_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec_ref(v_ctx_861_);
lean_dec(v_methods_860_);
return v_res_871_;
}
}
lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger(lean_object* v_goal_872_, lean_object* v_methods_873_, lean_object* v_ctx_874_, lean_object* v_s_875_, lean_object* v_e_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___redArg(v_goal_872_, v_methods_873_, v_ctx_874_, v_s_875_, v_e_876_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_887_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_872_ = stack[0].m_obj;
lean_object* v_methods_873_ = stack[1].m_obj;
lean_object* v_ctx_874_ = stack[2].m_obj;
lean_object* v_s_875_ = stack[3].m_obj;
lean_object* v_e_876_ = stack[4].m_obj;
lean_object* v_a_877_ = stack[5].m_obj;
lean_object* v_a_878_ = stack[6].m_obj;
lean_object* v_a_879_ = stack[7].m_obj;
lean_object* v_a_880_ = stack[8].m_obj;
lean_object* v_a_881_ = stack[9].m_obj;
lean_object* v_a_882_ = stack[10].m_obj;
lean_object* v_a_883_ = stack[11].m_obj;
lean_object* v_a_884_ = stack[12].m_obj;
lean_object* v_a_885_ = stack[13].m_obj;
lean_object* v_res_888_;
v_res_888_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger(v_goal_872_, v_methods_873_, v_ctx_874_, v_s_875_, v_e_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___boxed(lean_object* v_goal_889_, lean_object* v_methods_890_, lean_object* v_ctx_891_, lean_object* v_s_892_, lean_object* v_e_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger(v_goal_889_, v_methods_890_, v_ctx_891_, v_s_892_, v_e_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_ctx_891_);
lean_dec(v_methods_890_);
return v_res_904_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(lean_object* v_goal_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_st_ref_get(v_a_908_);
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
v___x_911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Grind_0__Lean_Meta_Grind_mkSymSimpDischarger___boxed), 15, 4);
lean_closure_set(v___x_911_, 0, v_goal_905_);
lean_closure_set(v___x_911_, 1, v_a_906_);
lean_closure_set(v___x_911_, 2, v_a_907_);
lean_closure_set(v___x_911_, 3, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_905_ = stack[0].m_obj;
lean_object* v_a_906_ = stack[1].m_obj;
lean_object* v_a_907_ = stack[2].m_obj;
lean_object* v_a_908_ = stack[3].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(v_goal_905_, v_a_906_, v_a_907_, v_a_908_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg___boxed(lean_object* v_goal_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(v_goal_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
return v_res_919_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger(lean_object* v_goal_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(v_goal_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_931_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_mkSymSimpDischarger_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_920_ = stack[0].m_obj;
lean_object* v_a_921_ = stack[1].m_obj;
lean_object* v_a_922_ = stack[2].m_obj;
lean_object* v_a_923_ = stack[3].m_obj;
lean_object* v_a_924_ = stack[4].m_obj;
lean_object* v_a_925_ = stack[5].m_obj;
lean_object* v_a_926_ = stack[6].m_obj;
lean_object* v_a_927_ = stack[7].m_obj;
lean_object* v_a_928_ = stack[8].m_obj;
lean_object* v_a_929_ = stack[9].m_obj;
lean_object* v_res_932_;
v_res_932_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger(v_goal_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___boxed(lean_object* v_goal_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger(v_goal_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
return v_res_944_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Grind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Grind(builtin);
}
#ifdef __cplusplus
}
#endif
