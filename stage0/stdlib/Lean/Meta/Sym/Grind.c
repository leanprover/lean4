// Lean compiler output
// Module: Lean.Meta.Sym.Grind
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Apply import Lean.Meta.Tactic.Grind.Main import Lean.Meta.Sym.Simp.Goal import Lean.Meta.Sym.Intro import Lean.Meta.Sym.Util import Lean.Meta.Tactic.Grind.Solve import Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v___x_12_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal___boxed(lean_object* v_mvarId_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Grind_mkGoal(v_mvarId_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx(lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(0u);
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(1u);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_IntrosResult_ctorIdx___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Grind_IntrosResult_ctorIdx(v_x_38_);
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
lean_dec_ref(v_t_40_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN(lean_object* v_goal_73_, lean_object* v_num_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_toGoalState_82_; lean_object* v_mvarId_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_120_; 
v_toGoalState_82_ = lean_ctor_get(v_goal_73_, 0);
v_mvarId_83_ = lean_ctor_get(v_goal_73_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_goal_73_);
if (v_isSharedCheck_120_ == 0)
{
v___x_85_ = v_goal_73_;
v_isShared_86_ = v_isSharedCheck_120_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_mvarId_83_);
lean_inc(v_toGoalState_82_);
lean_dec(v_goal_73_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_120_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Sym_introN(v_mvarId_83_, v_num_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_111_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_111_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_111_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_111_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
if (lean_obj_tag(v_a_88_) == 1)
{
lean_object* v_newDecls_92_; lean_object* v_mvarId_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_106_; 
v_newDecls_92_ = lean_ctor_get(v_a_88_, 0);
v_mvarId_93_ = lean_ctor_get(v_a_88_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_88_);
if (v_isSharedCheck_106_ == 0)
{
v___x_95_ = v_a_88_;
v_isShared_96_ = v_isSharedCheck_106_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_mvarId_93_);
lean_inc(v_newDecls_92_);
lean_dec(v_a_88_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_106_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_mvarId_93_);
v___x_98_ = v___x_85_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_toGoalState_82_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_mvarId_93_);
v___x_98_ = v_reuseFailAlloc_105_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___x_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_newDecls_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_104_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_100_);
v___x_102_ = v___x_90_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
else
{
lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_a_88_);
lean_del_object(v___x_85_);
lean_dec_ref(v_toGoalState_82_);
v___x_107_ = lean_box(0);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_107_);
v___x_109_ = v___x_90_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_del_object(v___x_85_);
lean_dec_ref(v_toGoalState_82_);
v_a_112_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_87_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_87_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object* v_goal_121_, lean_object* v_num_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Grind_Goal_introN(v_goal_121_, v_num_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros(lean_object* v_goal_131_, lean_object* v_names_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_toGoalState_140_; lean_object* v_mvarId_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_178_; 
v_toGoalState_140_ = lean_ctor_get(v_goal_131_, 0);
v_mvarId_141_ = lean_ctor_get(v_goal_131_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_goal_131_);
if (v_isSharedCheck_178_ == 0)
{
v___x_143_ = v_goal_131_;
v_isShared_144_ = v_isSharedCheck_178_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_mvarId_141_);
lean_inc(v_toGoalState_140_);
lean_dec(v_goal_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_178_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_Sym_intros(v_mvarId_141_, v_names_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_169_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_169_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_169_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_169_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
if (lean_obj_tag(v_a_146_) == 1)
{
lean_object* v_newDecls_150_; lean_object* v_mvarId_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_164_; 
v_newDecls_150_ = lean_ctor_get(v_a_146_, 0);
v_mvarId_151_ = lean_ctor_get(v_a_146_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_146_);
if (v_isSharedCheck_164_ == 0)
{
v___x_153_ = v_a_146_;
v_isShared_154_ = v_isSharedCheck_164_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_mvarId_151_);
lean_inc(v_newDecls_150_);
lean_dec(v_a_146_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_164_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v_mvarId_151_);
v___x_156_ = v___x_143_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_toGoalState_140_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_mvarId_151_);
v___x_156_ = v_reuseFailAlloc_163_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_newDecls_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_162_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_160_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_158_);
v___x_160_ = v___x_148_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_a_146_);
lean_del_object(v___x_143_);
lean_dec_ref(v_toGoalState_140_);
v___x_165_ = lean_box(0);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_165_);
v___x_167_ = v___x_148_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_del_object(v___x_143_);
lean_dec_ref(v_toGoalState_140_);
v_a_170_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_145_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_145_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object* v_goal_179_, lean_object* v_names_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Grind_Goal_intros(v_goal_179_, v_names_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(1u);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorIdx___boxed(lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_Grind_ApplyResult_ctorIdx(v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(lean_object* v_t_194_, lean_object* v_k_195_){
_start:
{
if (lean_obj_tag(v_t_194_) == 0)
{
return v_k_195_;
}
else
{
lean_object* v_subgoals_196_; lean_object* v___x_197_; 
v_subgoals_196_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_subgoals_196_);
lean_dec_ref(v_t_194_);
v___x_197_ = lean_apply_1(v_k_195_, v_subgoals_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim(lean_object* v_motive_198_, lean_object* v_ctorIdx_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_200_, v_k_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_ctorElim___boxed(lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Grind_ApplyResult_ctorElim(v_motive_204_, v_ctorIdx_205_, v_t_206_, v_h_207_, v_k_208_);
lean_dec(v_ctorIdx_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim___redArg(lean_object* v_t_210_, lean_object* v_failed_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_210_, v_failed_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_failed_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_failed_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_214_, v_failed_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim___redArg(lean_object* v_t_218_, lean_object* v_goals_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_218_, v_goals_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ApplyResult_goals_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_goals_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Grind_ApplyResult_ctorElim___redArg(v_t_222_, v_goals_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(lean_object* v_goal_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
if (lean_obj_tag(v_a_227_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = l_List_reverse___redArg(v_a_228_);
return v___x_229_;
}
else
{
lean_object* v_head_230_; lean_object* v_tail_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_head_230_ = lean_ctor_get(v_a_227_, 0);
v_tail_231_ = lean_ctor_get(v_a_227_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_a_227_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v_a_227_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_tail_231_);
lean_inc(v_head_230_);
lean_dec(v_a_227_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_toGoalState_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v_toGoalState_235_ = lean_ctor_get(v_goal_226_, 0);
lean_inc_ref(v_toGoalState_235_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_toGoalState_235_);
lean_ctor_set(v___x_236_, 1, v_head_230_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_a_228_);
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_a_228_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
v_a_227_ = v_tail_231_;
v_a_228_ = v___x_238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0___boxed(lean_object* v_goal_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(v_goal_242_, v_a_243_, v_a_244_);
lean_dec_ref(v_goal_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_apply(lean_object* v_goal_246_, lean_object* v_rule_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_mvarId_255_; lean_object* v___x_256_; 
v_mvarId_255_ = lean_ctor_get(v_goal_246_, 1);
lean_inc(v_mvarId_255_);
v___x_256_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_255_, v_rule_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_278_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_278_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_mvarIds_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_273_; 
v_mvarIds_261_ = lean_ctor_get(v_a_257_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_257_);
if (v_isSharedCheck_273_ == 0)
{
v___x_263_ = v_a_257_;
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_mvarIds_261_);
lean_dec(v_a_257_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_265_ = lean_box(0);
v___x_266_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Goal_apply_spec__0(v_goal_246_, v_mvarIds_261_, v___x_265_);
lean_dec_ref(v_goal_246_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_268_);
v___x_270_ = v___x_259_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_a_257_);
lean_dec_ref(v_goal_246_);
v___x_274_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_274_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_goal_246_);
v_a_279_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_256_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_256_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_apply___boxed(lean_object* v_goal_287_, lean_object* v_rule_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Grind_Goal_apply(v_goal_287_, v_rule_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx(lean_object* v_x_297_){
_start:
{
switch(lean_obj_tag(v_x_297_))
{
case 0:
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
return v___x_298_;
}
case 1:
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(1u);
return v___x_299_;
}
default: 
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(2u);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorIdx___boxed(lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Grind_SimpGoalResult_ctorIdx(v_x_301_);
lean_dec(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(lean_object* v_t_303_, lean_object* v_k_304_){
_start:
{
if (lean_obj_tag(v_t_303_) == 2)
{
lean_object* v_goal_305_; lean_object* v___x_306_; 
v_goal_305_ = lean_ctor_get(v_t_303_, 0);
lean_inc_ref(v_goal_305_);
lean_dec_ref(v_t_303_);
v___x_306_ = lean_apply_1(v_k_304_, v_goal_305_);
return v___x_306_;
}
else
{
lean_dec(v_t_303_);
return v_k_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim(lean_object* v_motive_307_, lean_object* v_ctorIdx_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_k_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_309_, v_k_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_ctorElim___boxed(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim(v_motive_313_, v_ctorIdx_314_, v_t_315_, v_h_316_, v_k_317_);
lean_dec(v_ctorIdx_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim___redArg(lean_object* v_t_319_, lean_object* v_noProgress_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_319_, v_noProgress_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_noProgress_elim(lean_object* v_motive_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_noProgress_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_323_, v_noProgress_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim___redArg(lean_object* v_t_327_, lean_object* v_closed_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_327_, v_closed_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_closed_elim(lean_object* v_motive_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_closed_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_331_, v_closed_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim___redArg(lean_object* v_t_335_, lean_object* v_goal_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_335_, v_goal_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SimpGoalResult_goal_elim(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_goal_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Grind_SimpGoalResult_ctorElim___redArg(v_t_339_, v_goal_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simp(lean_object* v_goal_343_, lean_object* v_methods_344_, lean_object* v_config_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_toGoalState_353_; lean_object* v_mvarId_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_394_; 
v_toGoalState_353_ = lean_ctor_get(v_goal_343_, 0);
v_mvarId_354_ = lean_ctor_get(v_goal_343_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_goal_343_);
if (v_isSharedCheck_394_ == 0)
{
v___x_356_ = v_goal_343_;
v_isShared_357_ = v_isSharedCheck_394_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_mvarId_354_);
lean_inc(v_toGoalState_353_);
lean_dec(v_goal_343_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_394_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_354_, v_methods_344_, v_config_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_385_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_385_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
switch(lean_obj_tag(v_a_359_))
{
case 0:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_del_object(v___x_356_);
lean_dec_ref(v_toGoalState_353_);
v___x_363_ = lean_box(0);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
case 1:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_del_object(v___x_356_);
lean_dec_ref(v_toGoalState_353_);
v___x_367_ = lean_box(1);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_367_);
v___x_369_ = v___x_361_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
default: 
{
lean_object* v_mvarId_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_384_; 
v_mvarId_371_ = lean_ctor_get(v_a_359_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_359_);
if (v_isSharedCheck_384_ == 0)
{
v___x_373_ = v_a_359_;
v_isShared_374_ = v_isSharedCheck_384_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_mvarId_371_);
lean_dec(v_a_359_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_384_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v_mvarId_371_);
v___x_376_ = v___x_356_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_toGoalState_353_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_mvarId_371_);
v___x_376_ = v_reuseFailAlloc_383_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_376_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_378_);
v___x_380_ = v___x_361_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
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
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_del_object(v___x_356_);
lean_dec_ref(v_toGoalState_353_);
v_a_386_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_358_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_358_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simp___boxed(lean_object* v_goal_395_, lean_object* v_methods_396_, lean_object* v_config_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Grind_Goal_simp(v_goal_395_, v_methods_396_, v_config_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(lean_object* v_goal_406_, lean_object* v_methods_407_, lean_object* v_config_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_toGoalState_416_; lean_object* v_mvarId_417_; lean_object* v___x_418_; 
v_toGoalState_416_ = lean_ctor_get(v_goal_406_, 0);
v_mvarId_417_ = lean_ctor_get(v_goal_406_, 1);
lean_inc(v_mvarId_417_);
v___x_418_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_417_, v_methods_407_, v_config_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_451_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_451_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_451_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_451_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
switch(lean_obj_tag(v_a_419_))
{
case 0:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_423_, 0, v_goal_406_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
case 1:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_dec_ref(v_goal_406_);
v___x_427_ = lean_box(1);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_427_);
v___x_429_ = v___x_421_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
default: 
{
lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_448_; 
lean_inc_ref(v_toGoalState_416_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_goal_406_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_goal_406_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_goal_406_, 0);
lean_dec(v_unused_450_);
v___x_432_ = v_goal_406_;
v_isShared_433_ = v_isSharedCheck_448_;
goto v_resetjp_431_;
}
else
{
lean_dec(v_goal_406_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_448_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_mvarId_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_447_; 
v_mvarId_434_ = lean_ctor_get(v_a_419_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_447_ == 0)
{
v___x_436_ = v_a_419_;
v_isShared_437_ = v_isSharedCheck_447_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_mvarId_434_);
lean_dec(v_a_419_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_447_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_mvarId_434_);
v___x_439_ = v___x_432_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_toGoalState_416_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_mvarId_434_);
v___x_439_ = v_reuseFailAlloc_446_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_441_);
v___x_443_ = v___x_421_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
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
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_goal_406_);
v_a_452_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_418_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_418_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress___boxed(lean_object* v_goal_460_, lean_object* v_methods_461_, lean_object* v_config_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_Grind_Goal_simpIgnoringNoProgress(v_goal_460_, v_methods_461_, v_config_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalize(lean_object* v_goal_471_, lean_object* v_num_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_num_472_);
v___x_484_ = l_Lean_Meta_Grind_processHypotheses(v_goal_471_, v___x_483_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalize___boxed(lean_object* v_goal_485_, lean_object* v_num_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Grind_Goal_internalize(v_goal_485_, v_num_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalizeAll(lean_object* v_goal_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_box(0);
v___x_510_ = l_Lean_Meta_Grind_processHypotheses(v_goal_498_, v___x_509_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object* v_goal_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Grind_Goal_internalizeAll(v_goal_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx(lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v___x_524_; 
v___x_524_ = lean_unsigned_to_nat(0u);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_unsigned_to_nat(1u);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorIdx___boxed(lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Grind_GrindResult_ctorIdx(v_x_526_);
lean_dec(v_x_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(lean_object* v_t_528_, lean_object* v_k_529_){
_start:
{
if (lean_obj_tag(v_t_528_) == 0)
{
lean_object* v_goal_530_; lean_object* v___x_531_; 
v_goal_530_ = lean_ctor_get(v_t_528_, 0);
lean_inc_ref(v_goal_530_);
lean_dec_ref(v_t_528_);
v___x_531_ = lean_apply_1(v_k_529_, v_goal_530_);
return v___x_531_;
}
else
{
return v_k_529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim(lean_object* v_motive_532_, lean_object* v_ctorIdx_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_k_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_534_, v_k_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_ctorElim___boxed(lean_object* v_motive_538_, lean_object* v_ctorIdx_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_Grind_GrindResult_ctorElim(v_motive_538_, v_ctorIdx_539_, v_t_540_, v_h_541_, v_k_542_);
lean_dec(v_ctorIdx_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim___redArg(lean_object* v_t_544_, lean_object* v_failed_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_544_, v_failed_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_failed_elim(lean_object* v_motive_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_failed_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_548_, v_failed_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim___redArg(lean_object* v_t_552_, lean_object* v_closed_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_552_, v_closed_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindResult_closed_elim(lean_object* v_motive_555_, lean_object* v_t_556_, lean_object* v_h_557_, lean_object* v_closed_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Grind_GrindResult_ctorElim___redArg(v_t_556_, v_closed_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_grind(lean_object* v_goal_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_solve(v_goal_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_591_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_591_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_val_576_ = lean_ctor_get(v_a_572_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_a_572_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_a_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_576_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_581_);
v___x_583_ = v___x_574_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec(v_a_572_);
v___x_587_ = lean_box(1);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_587_);
v___x_589_ = v___x_574_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_571_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_571_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_grind___boxed(lean_object* v_goal_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Grind_Goal_grind(v_goal_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_assumption(lean_object* v_goal_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_mvarId_618_; lean_object* v___x_619_; 
v_mvarId_618_ = lean_ctor_get(v_goal_612_, 1);
lean_inc(v_mvarId_618_);
lean_dec_ref(v_goal_612_);
v___x_619_ = l_Lean_MVarId_assumptionCore(v_mvarId_618_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_assumption___boxed(lean_object* v_goal_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Grind_Goal_assumption(v_goal_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_626_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
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
