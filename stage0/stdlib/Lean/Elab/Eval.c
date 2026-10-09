// Lean compiler output
// Module: Lean.Elab.Eval
// Imports: public import Lean.Meta.Eval public import Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(v_e_31_, v___y_35_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v_res_40_;
v_res_40_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = l_Lean_Elab_abortTermExceptionId;
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
return v___x_52_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___closed__0);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg___boxed(lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
return v_res_58_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(lean_object* v_00_u03b1_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_60_ = stack[1].m_obj;
lean_object* v___y_61_ = stack[2].m_obj;
lean_object* v___y_62_ = stack[3].m_obj;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(lean_box(0), v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___boxed(lean_object* v_00_u03b1_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1(v_00_u03b1_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_77_;
}
}
lean_object* l_Lean_Elab_Term_evalTerm___redArg___lam__0(lean_object* v_value_78_, lean_object* v___x_79_, uint8_t v___x_80_, lean_object* v___x_81_, lean_object* v_type_82_, uint8_t v_safety_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_78_, v___x_79_, v___x_80_, v___x_80_, v___x_81_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; uint8_t v___x_93_; lean_object* v___x_94_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = 0;
v___x_94_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_93_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_95_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_evalTerm_spec__0___redArg(v_a_92_, v___y_87_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_n(v_a_96_, 2);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = l_Lean_Meta_getMVars(v_a_96_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = lean_box(0);
v___x_100_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_98_, v___x_99_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v_a_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; uint8_t v___x_102_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_102_ = lean_unbox(v_a_101_);
lean_dec(v_a_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_evalExpr___redArg(v_type_82_, v_a_96_, v_safety_83_, v___x_80_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_evalTerm_spec__1___redArg();
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v___x_105_; 
lean_dec_ref_known(v___x_104_, 1);
v___x_105_ = l_Lean_Meta_evalExpr___redArg(v_type_82_, v_a_96_, v_safety_83_, v___x_80_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_105_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_a_96_);
lean_dec_ref(v_type_82_);
v_a_106_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_104_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_dec(v_a_96_);
lean_dec_ref(v_type_82_);
v_a_114_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_100_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_100_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_a_96_);
lean_dec_ref(v_type_82_);
v_a_122_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_97_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_97_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec_ref(v_type_82_);
v_a_130_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_95_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_95_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_92_);
lean_dec_ref(v_type_82_);
v_a_138_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_94_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_94_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v_type_82_);
v_a_146_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_91_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_91_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_evalTerm___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_78_ = stack[0].m_obj;
lean_object* v___x_79_ = stack[1].m_obj;
uint8_t v___x_80_ = stack[2].m_num;
lean_object* v___x_81_ = stack[3].m_obj;
lean_object* v_type_82_ = stack[4].m_obj;
uint8_t v_safety_83_ = stack[5].m_num;
lean_object* v___y_84_ = stack[6].m_obj;
lean_object* v___y_85_ = stack[7].m_obj;
lean_object* v___y_86_ = stack[8].m_obj;
lean_object* v___y_87_ = stack[9].m_obj;
lean_object* v___y_88_ = stack[10].m_obj;
lean_object* v___y_89_ = stack[11].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Elab_Term_evalTerm___redArg___lam__0(v_value_78_, v___x_79_, v___x_80_, v___x_81_, v_type_82_, v_safety_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg___lam__0___boxed(lean_object* v_value_155_, lean_object* v___x_156_, lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v_type_159_, lean_object* v_safety_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___x_3657__boxed_168_; uint8_t v_safety_boxed_169_; lean_object* v_res_170_; 
v___x_3657__boxed_168_ = lean_unbox(v___x_157_);
v_safety_boxed_169_ = lean_unbox(v_safety_160_);
v_res_170_ = l_Lean_Elab_Term_evalTerm___redArg___lam__0(v_value_155_, v___x_156_, v___x_3657__boxed_168_, v___x_158_, v_type_159_, v_safety_boxed_169_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_171_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__0);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__1);
v___x_177_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
lean_ctor_set(v___x_177_, 3, v___x_176_);
lean_ctor_set(v___x_177_, 4, v___x_176_);
lean_ctor_set(v___x_177_, 5, v___x_176_);
return v___x_177_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(lean_object* v_env_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_nextMacroScope_183_; lean_object* v_ngen_184_; lean_object* v_auxDeclNGen_185_; lean_object* v_traceState_186_; lean_object* v_recordedDeps_187_; lean_object* v_messages_188_; lean_object* v_infoState_189_; lean_object* v_snapshotTasks_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_216_; 
v___x_182_ = lean_st_ref_take(v___y_180_);
v_nextMacroScope_183_ = lean_ctor_get(v___x_182_, 1);
v_ngen_184_ = lean_ctor_get(v___x_182_, 2);
v_auxDeclNGen_185_ = lean_ctor_get(v___x_182_, 3);
v_traceState_186_ = lean_ctor_get(v___x_182_, 4);
v_recordedDeps_187_ = lean_ctor_get(v___x_182_, 6);
v_messages_188_ = lean_ctor_get(v___x_182_, 7);
v_infoState_189_ = lean_ctor_get(v___x_182_, 8);
v_snapshotTasks_190_ = lean_ctor_get(v___x_182_, 9);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_217_ = lean_ctor_get(v___x_182_, 5);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v___x_182_, 0);
lean_dec(v_unused_218_);
v___x_192_ = v___x_182_;
v_isShared_193_ = v_isSharedCheck_216_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snapshotTasks_190_);
lean_inc(v_infoState_189_);
lean_inc(v_messages_188_);
lean_inc(v_recordedDeps_187_);
lean_inc(v_traceState_186_);
lean_inc(v_auxDeclNGen_185_);
lean_inc(v_ngen_184_);
lean_inc(v_nextMacroScope_183_);
lean_dec(v___x_182_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_216_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__2);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 5, v___x_194_);
lean_ctor_set(v___x_192_, 0, v_env_178_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_env_178_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_nextMacroScope_183_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_ngen_184_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_auxDeclNGen_185_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_215_, 5, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_215_, 6, v_recordedDeps_187_);
lean_ctor_set(v_reuseFailAlloc_215_, 7, v_messages_188_);
lean_ctor_set(v_reuseFailAlloc_215_, 8, v_infoState_189_);
lean_ctor_set(v_reuseFailAlloc_215_, 9, v_snapshotTasks_190_);
v___x_196_ = v_reuseFailAlloc_215_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_mctx_199_; lean_object* v_zetaDeltaFVarIds_200_; lean_object* v_postponed_201_; lean_object* v_diag_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_213_; 
v___x_197_ = lean_st_ref_put(v___y_180_, v___x_196_);
v___x_198_ = lean_st_ref_take(v___y_179_);
v_mctx_199_ = lean_ctor_get(v___x_198_, 0);
v_zetaDeltaFVarIds_200_ = lean_ctor_get(v___x_198_, 2);
v_postponed_201_ = lean_ctor_get(v___x_198_, 3);
v_diag_202_ = lean_ctor_get(v___x_198_, 4);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v___x_198_, 1);
lean_dec(v_unused_214_);
v___x_204_ = v___x_198_;
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_diag_202_);
lean_inc(v_postponed_201_);
lean_inc(v_zetaDeltaFVarIds_200_);
lean_inc(v_mctx_199_);
lean_dec(v___x_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = lean_box(0);
v___x_207_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___closed__3);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_mctx_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_zetaDeltaFVarIds_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_postponed_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_diag_202_);
v___x_209_ = v_reuseFailAlloc_212_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_st_ref_put(v___y_179_, v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_206_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_178_ = stack[0].m_obj;
lean_object* v___y_179_ = stack[1].m_obj;
lean_object* v___y_180_ = stack[2].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_178_, v___y_179_, v___y_180_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg___boxed(lean_object* v_env_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec(v___y_221_);
return v_res_224_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(lean_object* v_env_225_, lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v_a_237_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
v___x_247_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_225_, v___y_230_, v___y_232_);
lean_dec_ref(v___x_247_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
v___x_248_ = lean_apply_7(v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, lean_box(0));
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_235_, v___y_230_, v___y_232_);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_250_, 0);
lean_dec(v_unused_258_);
v___x_252_ = v___x_250_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_dec(v___x_250_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_a_249_);
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_249_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_259_; 
v_a_259_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_248_, 1);
v_a_237_ = v_a_259_;
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v___x_238_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_235_, v___y_230_, v___y_232_);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_246_);
v___x_240_ = v___x_238_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_dec(v___x_238_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 1);
lean_ctor_set(v___x_240_, 0, v_a_237_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_237_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_225_ = stack[0].m_obj;
lean_object* v_x_226_ = stack[1].m_obj;
lean_object* v___y_227_ = stack[2].m_obj;
lean_object* v___y_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v___y_230_ = stack[5].m_obj;
lean_object* v___y_231_ = stack[6].m_obj;
lean_object* v___y_232_ = stack[7].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(v_env_225_, v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg___boxed(lean_object* v_env_261_, lean_object* v_x_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(v_env_261_, v_x_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_270_;
}
}
lean_object* l_Lean_Elab_Term_evalTerm___redArg(lean_object* v_type_271_, lean_object* v_value_272_, uint8_t v_safety_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc_ref(v_type_271_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_type_271_);
v___x_282_ = 1;
v___x_283_ = lean_box(0);
v___x_284_ = lean_box(v___x_282_);
v___x_285_ = lean_box(v_safety_273_);
v___f_286_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_evalTerm___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_286_, 0, v_value_272_);
lean_closure_set(v___f_286_, 1, v___x_281_);
lean_closure_set(v___f_286_, 2, v___x_284_);
lean_closure_set(v___f_286_, 3, v___x_283_);
lean_closure_set(v___f_286_, 4, v_type_271_);
lean_closure_set(v___f_286_, 5, v___x_285_);
v___x_287_ = lean_st_ref_get(v_a_279_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = l_Lean_Environment_unlockAsync(v_env_288_);
v___x_290_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(v___x_289_, v___f_286_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_evalTerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_271_ = stack[0].m_obj;
lean_object* v_value_272_ = stack[1].m_obj;
uint8_t v_safety_273_ = stack[2].m_num;
lean_object* v_a_274_ = stack[3].m_obj;
lean_object* v_a_275_ = stack[4].m_obj;
lean_object* v_a_276_ = stack[5].m_obj;
lean_object* v_a_277_ = stack[6].m_obj;
lean_object* v_a_278_ = stack[7].m_obj;
lean_object* v_a_279_ = stack[8].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_Elab_Term_evalTerm___redArg(v_type_271_, v_value_272_, v_safety_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___redArg___boxed(lean_object* v_type_292_, lean_object* v_value_293_, lean_object* v_safety_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
uint8_t v_safety_boxed_302_; lean_object* v_res_303_; 
v_safety_boxed_302_ = lean_unbox(v_safety_294_);
v_res_303_ = l_Lean_Elab_Term_evalTerm___redArg(v_type_292_, v_value_293_, v_safety_boxed_302_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_303_;
}
}
lean_object* l_Lean_Elab_Term_evalTerm(lean_object* v_00_u03b1_304_, lean_object* v_type_305_, lean_object* v_value_306_, uint8_t v_safety_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Elab_Term_evalTerm___redArg(v_type_305_, v_value_306_, v_safety_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_305_ = stack[1].m_obj;
lean_object* v_value_306_ = stack[2].m_obj;
uint8_t v_safety_307_ = stack[3].m_num;
lean_object* v_a_308_ = stack[4].m_obj;
lean_object* v_a_309_ = stack[5].m_obj;
lean_object* v_a_310_ = stack[6].m_obj;
lean_object* v_a_311_ = stack[7].m_obj;
lean_object* v_a_312_ = stack[8].m_obj;
lean_object* v_a_313_ = stack[9].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_Lean_Elab_Term_evalTerm(lean_box(0), v_type_305_, v_value_306_, v_safety_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_evalTerm___boxed(lean_object* v_00_u03b1_317_, lean_object* v_type_318_, lean_object* v_value_319_, lean_object* v_safety_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
uint8_t v_safety_boxed_328_; lean_object* v_res_329_; 
v_safety_boxed_328_ = lean_unbox(v_safety_320_);
v_res_329_ = l_Lean_Elab_Term_evalTerm(v_00_u03b1_317_, v_type_318_, v_value_319_, v_safety_boxed_328_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_329_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(lean_object* v_env_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___redArg(v_env_330_, v___y_334_, v___y_336_);
return v___x_338_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_330_ = stack[0].m_obj;
lean_object* v___y_331_ = stack[1].m_obj;
lean_object* v___y_332_ = stack[2].m_obj;
lean_object* v___y_333_ = stack[3].m_obj;
lean_object* v___y_334_ = stack[4].m_obj;
lean_object* v___y_335_ = stack[5].m_obj;
lean_object* v___y_336_ = stack[6].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(v_env_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2___boxed(lean_object* v_env_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_spec__2(v_env_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_348_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(lean_object* v_00_u03b1_349_, lean_object* v_env_350_, lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___redArg(v_env_350_, v_x_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_350_ = stack[1].m_obj;
lean_object* v_x_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v___y_353_ = stack[4].m_obj;
lean_object* v___y_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v___y_356_ = stack[7].m_obj;
lean_object* v___y_357_ = stack[8].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(lean_box(0), v_env_350_, v_x_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2___boxed(lean_object* v_00_u03b1_361_, lean_object* v_env_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_withEnv___at___00Lean_Elab_Term_evalTerm_spec__2(v_00_u03b1_361_, v_env_362_, v_x_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_371_;
}
}
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Eval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Eval(builtin);
}
#ifdef __cplusplus
}
#endif
