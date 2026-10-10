// Lean compiler output
// Module: Lean.Meta.Match.Value
// Imports: public import Lean.Meta.LitValues
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFloatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFloat32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_isMatchValue(lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; lean_object* v_a_53_; lean_object* v___x_54_; 
v___x_52_ = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(v_e_46_, v_a_48_);
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref(v___x_52_);
v___x_54_ = l_Lean_Meta_getNatValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_255_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_255_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_255_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_255_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
if (lean_obj_tag(v_a_55_) == 0)
{
uint8_t v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; 
lean_del_object(v___x_57_);
v___x_59_ = 0;
v___x_60_ = 1;
lean_inc(v_a_53_);
v___x_61_ = l_Lean_Meta_getIntValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_241_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_241_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_241_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_241_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_66_; 
lean_del_object(v___x_64_);
lean_inc(v_a_53_);
v___x_66_ = l_Lean_Meta_getFinValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_228_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_228_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_228_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_228_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v___x_71_; 
lean_del_object(v___x_69_);
lean_inc(v_a_53_);
v___x_71_ = l_Lean_Meta_getBitVecValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_215_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_215_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_215_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_215_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
if (lean_obj_tag(v_a_72_) == 0)
{
lean_object* v___x_76_; 
lean_inc(v_a_53_);
v___x_76_ = l_Lean_Meta_getStringValue_x3f(v_a_53_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v___x_77_; 
lean_del_object(v___x_74_);
lean_inc(v_a_53_);
v___x_77_ = l_Lean_Meta_getCharValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_198_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_198_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_198_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_198_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v___x_82_; 
lean_del_object(v___x_80_);
lean_inc(v_a_53_);
v___x_82_ = l_Lean_Meta_getUInt8Value_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_185_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_185_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_185_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_185_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
if (lean_obj_tag(v_a_83_) == 0)
{
lean_object* v___x_87_; 
lean_del_object(v___x_85_);
lean_inc(v_a_53_);
v___x_87_ = l_Lean_Meta_getUInt16Value_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_172_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_172_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_172_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_172_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
if (lean_obj_tag(v_a_88_) == 0)
{
lean_object* v___x_92_; 
lean_del_object(v___x_90_);
lean_inc(v_a_53_);
v___x_92_ = l_Lean_Meta_getUInt32Value_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_159_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_159_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_159_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_159_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
if (lean_obj_tag(v_a_93_) == 0)
{
lean_object* v___x_97_; 
lean_del_object(v___x_95_);
lean_inc(v_a_53_);
v___x_97_ = l_Lean_Meta_getUInt64Value_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_146_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_146_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_146_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_146_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
if (lean_obj_tag(v_a_98_) == 0)
{
lean_object* v___x_102_; 
lean_del_object(v___x_100_);
lean_inc(v_a_53_);
v___x_102_ = l_Lean_Meta_getFloatValue_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_133_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_133_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
if (lean_obj_tag(v_a_103_) == 0)
{
lean_object* v___x_107_; 
lean_del_object(v___x_105_);
v___x_107_ = l_Lean_Meta_getFloat32Value_x3f(v_a_53_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_120_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_120_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_box(v___x_59_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_dec_ref_known(v_a_108_, 1);
v___x_116_ = lean_box(v___x_60_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_116_);
v___x_118_ = v___x_110_;
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
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_107_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_107_);
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
else
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_dec_ref_known(v_a_103_, 1);
lean_dec(v_a_53_);
v___x_129_ = lean_box(v___x_60_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_129_);
v___x_131_ = v___x_105_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_53_);
v_a_134_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_102_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_102_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec_ref_known(v_a_98_, 1);
lean_dec(v_a_53_);
v___x_142_ = lean_box(v___x_60_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_142_);
v___x_144_ = v___x_100_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_a_53_);
v_a_147_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_97_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_97_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec_ref_known(v_a_93_, 1);
lean_dec(v_a_53_);
v___x_155_ = lean_box(v___x_60_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_155_);
v___x_157_ = v___x_95_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_a_53_);
v_a_160_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_92_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_92_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
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
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec_ref_known(v_a_88_, 1);
lean_dec(v_a_53_);
v___x_168_ = lean_box(v___x_60_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_168_);
v___x_170_ = v___x_90_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_a_53_);
v_a_173_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_87_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_87_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref_known(v_a_83_, 1);
lean_dec(v_a_53_);
v___x_181_ = lean_box(v___x_60_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_181_);
v___x_183_ = v___x_85_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_a_53_);
v_a_186_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_82_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_82_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec_ref_known(v_a_78_, 1);
lean_dec(v_a_53_);
v___x_194_ = lean_box(v___x_60_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_194_);
v___x_196_ = v___x_80_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_53_);
v_a_199_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_77_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_77_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec_ref_known(v___x_76_, 1);
lean_dec(v_a_53_);
v___x_207_ = lean_box(v___x_60_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_207_);
v___x_209_ = v___x_74_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref_known(v_a_72_, 1);
lean_dec(v_a_53_);
v___x_211_ = lean_box(v___x_60_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_211_);
v___x_213_ = v___x_74_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_a_53_);
v_a_216_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_71_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_71_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_dec_ref_known(v_a_67_, 1);
lean_dec(v_a_53_);
v___x_224_ = lean_box(v___x_60_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_224_);
v___x_226_ = v___x_69_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_a_53_);
v_a_229_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_66_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_66_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec_ref_known(v_a_62_, 1);
lean_dec(v_a_53_);
v___x_237_ = lean_box(v___x_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_237_);
v___x_239_ = v___x_64_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_a_53_);
v_a_242_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_61_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_61_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec_ref_known(v_a_55_, 1);
lean_dec(v_a_53_);
v___x_250_ = 1;
v___x_251_ = lean_box(v___x_250_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_251_);
v___x_253_ = v___x_57_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_53_);
v_a_256_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_54_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_54_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isMatchValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_46_ = stack[0].m_obj;
lean_object* v_a_47_ = stack[1].m_obj;
lean_object* v_a_48_ = stack[2].m_obj;
lean_object* v_a_49_ = stack[3].m_obj;
lean_object* v_a_50_ = stack[4].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Meta_isMatchValue(v_e_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_isMatchValue(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_271_;
}
}
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Value(builtin);
}
#ifdef __cplusplus
}
#endif
