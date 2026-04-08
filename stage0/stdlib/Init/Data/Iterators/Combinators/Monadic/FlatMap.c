// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.FlatMap
// Imports: public import Init.Data.Iterators.Combinators.Monadic.FilterMap import Init.Data.Option.Lemmas
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_flatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___redArg(lean_object* v_it_u2081_1_, lean_object* v_it_u2082_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_it_u2081_1_);
lean_ctor_set(v___x_3_, 1, v_it_u2082_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b1_u2082_5_, lean_object* v_00_u03b2_6_, lean_object* v_m_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_it_u2081_11_, lean_object* v_it_u2082_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v_it_u2081_11_);
lean_ctor_set(v___x_13_, 1, v_it_u2082_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___boxed(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b1_u2082_15_, lean_object* v_00_u03b2_16_, lean_object* v_m_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_it_u2081_21_, lean_object* v_it_u2082_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter(v_00_u03b1_14_, v_00_u03b1_u2082_15_, v_00_u03b2_16_, v_m_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_it_u2081_21_, v_it_u2082_22_);
lean_dec(v_inst_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM___redArg(lean_object* v_it_u2081_24_, lean_object* v_it_u2082_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_it_u2081_24_);
lean_ctor_set(v___x_26_, 1, v_it_u2082_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_00_u03b1_u2082_29_, lean_object* v_00_u03b3_30_, lean_object* v_m_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_f_36_, lean_object* v_it_u2081_37_, lean_object* v_it_u2082_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_it_u2081_37_);
lean_ctor_set(v___x_39_, 1, v_it_u2082_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfterM___boxed(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_00_u03b1_u2082_42_, lean_object* v_00_u03b3_43_, lean_object* v_m_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_f_49_, lean_object* v_it_u2081_50_, lean_object* v_it_u2082_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_IterM_flatMapAfterM(v_00_u03b1_40_, v_00_u03b2_41_, v_00_u03b1_u2082_42_, v_00_u03b3_43_, v_m_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_f_49_, v_it_u2081_50_, v_it_u2082_51_);
lean_dec(v_f_49_);
lean_dec(v_inst_48_);
lean_dec(v_inst_47_);
lean_dec(v_inst_46_);
lean_dec_ref(v_inst_45_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM___redArg(lean_object* v_it_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_box(0);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_it_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_00_u03b1_u2082_58_, lean_object* v_00_u03b3_59_, lean_object* v_m_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_f_65_, lean_object* v_it_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_it_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapM___boxed(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_00_u03b1_u2082_71_, lean_object* v_00_u03b3_72_, lean_object* v_m_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_f_78_, lean_object* v_it_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_IterM_flatMapM(v_00_u03b1_69_, v_00_u03b2_70_, v_00_u03b1_u2082_71_, v_00_u03b3_72_, v_m_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_inst_77_, v_f_78_, v_it_79_);
lean_dec(v_f_78_);
lean_dec(v_inst_77_);
lean_dec(v_inst_76_);
lean_dec(v_inst_75_);
lean_dec_ref(v_inst_74_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter___redArg(lean_object* v_it_u2081_81_, lean_object* v_it_u2082_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_it_u2081_81_);
lean_ctor_set(v___x_83_, 1, v_it_u2082_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_00_u03b1_u2082_86_, lean_object* v_00_u03b3_87_, lean_object* v_m_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_f_92_, lean_object* v_it_u2081_93_, lean_object* v_it_u2082_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_it_u2081_93_);
lean_ctor_set(v___x_95_, 1, v_it_u2082_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMapAfter___boxed(lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_00_u03b1_u2082_98_, lean_object* v_00_u03b3_99_, lean_object* v_m_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_f_104_, lean_object* v_it_u2081_105_, lean_object* v_it_u2082_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_IterM_flatMapAfter(v_00_u03b1_96_, v_00_u03b2_97_, v_00_u03b1_u2082_98_, v_00_u03b3_99_, v_m_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_f_104_, v_it_u2081_105_, v_it_u2082_106_);
lean_dec(v_f_104_);
lean_dec(v_inst_103_);
lean_dec(v_inst_102_);
lean_dec_ref(v_inst_101_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMap___redArg(lean_object* v_it_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_box(0);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_it_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMap(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_00_u03b1_u2082_113_, lean_object* v_00_u03b3_114_, lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_f_119_, lean_object* v_it_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_it_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_flatMap___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_00_u03b1_u2082_125_, lean_object* v_00_u03b3_126_, lean_object* v_m_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_f_131_, lean_object* v_it_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_IterM_flatMap(v_00_u03b1_123_, v_00_u03b2_124_, v_00_u03b1_u2082_125_, v_00_u03b3_126_, v_m_127_, v_inst_128_, v_inst_129_, v_inst_130_, v_f_131_, v_it_132_);
lean_dec(v_f_131_);
lean_dec(v_inst_130_);
lean_dec(v_inst_129_);
lean_dec_ref(v_inst_128_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0(lean_object* v_toPure_134_, lean_object* v_it_u2082_135_, lean_object* v_____do__lift_136_){
_start:
{
switch(lean_obj_tag(v_____do__lift_136_))
{
case 0:
{
lean_object* v_it_137_; lean_object* v_out_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_it_u2082_135_);
v_it_137_ = lean_ctor_get(v_____do__lift_136_, 0);
lean_inc(v_it_137_);
v_out_138_ = lean_ctor_get(v_____do__lift_136_, 1);
lean_inc(v_out_138_);
lean_dec_ref(v_____do__lift_136_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_out_138_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_it_137_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
v___x_142_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_141_);
return v___x_142_;
}
case 1:
{
lean_object* v_it_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v_it_143_ = lean_ctor_get(v_____do__lift_136_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_____do__lift_136_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v_____do__lift_136_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_it_143_);
lean_dec(v_____do__lift_136_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_it_143_);
lean_ctor_set(v___x_147_, 1, v_it_u2082_135_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_149_);
return v___x_150_;
}
}
}
default: 
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_it_u2082_135_);
v___x_153_ = lean_box(2);
v___x_154_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_153_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1(lean_object* v_it_u2081_155_, lean_object* v_toPure_156_, lean_object* v_____do__lift_157_){
_start:
{
switch(lean_obj_tag(v_____do__lift_157_))
{
case 0:
{
lean_object* v_it_158_; lean_object* v_out_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_169_; 
v_it_158_ = lean_ctor_get(v_____do__lift_157_, 0);
v_out_159_ = lean_ctor_get(v_____do__lift_157_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_____do__lift_157_);
if (v_isSharedCheck_169_ == 0)
{
v___x_161_ = v_____do__lift_157_;
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_out_159_);
lean_inc(v_it_158_);
lean_dec(v_____do__lift_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_it_158_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_it_u2081_155_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_out_159_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_166_);
return v___x_167_;
}
}
}
case 1:
{
lean_object* v_it_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_it_170_ = lean_ctor_get(v_____do__lift_157_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_____do__lift_157_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v_____do__lift_157_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_it_170_);
lean_dec(v_____do__lift_157_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_it_170_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_it_u2081_155_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_177_);
return v___x_178_;
}
}
}
default: 
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_it_u2081_155_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
v___x_184_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__2(lean_object* v_toPure_185_, lean_object* v_inst_186_, lean_object* v_toBind_187_, lean_object* v_inst_188_, lean_object* v_it_189_){
_start:
{
lean_object* v_it_u2082_190_; 
v_it_u2082_190_ = lean_ctor_get(v_it_189_, 1);
lean_inc(v_it_u2082_190_);
if (lean_obj_tag(v_it_u2082_190_) == 0)
{
lean_object* v_it_u2081_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_inst_188_);
v_it_u2081_191_ = lean_ctor_get(v_it_189_, 0);
lean_inc(v_it_u2081_191_);
lean_dec_ref(v_it_189_);
v___f_192_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0), 3, 2);
lean_closure_set(v___f_192_, 0, v_toPure_185_);
lean_closure_set(v___f_192_, 1, v_it_u2082_190_);
v___x_193_ = lean_apply_1(v_inst_186_, v_it_u2081_191_);
v___x_194_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_193_, v___f_192_);
return v___x_194_;
}
else
{
lean_object* v_it_u2081_195_; lean_object* v_val_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_inst_186_);
v_it_u2081_195_ = lean_ctor_get(v_it_189_, 0);
lean_inc(v_it_u2081_195_);
lean_dec_ref(v_it_189_);
v_val_196_ = lean_ctor_get(v_it_u2082_190_, 0);
lean_inc(v_val_196_);
lean_dec_ref(v_it_u2082_190_);
v___f_197_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_197_, 0, v_it_u2081_195_);
lean_closure_set(v___f_197_, 1, v_toPure_185_);
v___x_198_ = lean_apply_1(v_inst_188_, v_val_196_);
v___x_199_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_198_, v___f_197_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v_toApplicative_203_; lean_object* v_toBind_204_; lean_object* v_toPure_205_; lean_object* v___f_206_; 
v_toApplicative_203_ = lean_ctor_get(v_inst_200_, 0);
lean_inc_ref(v_toApplicative_203_);
v_toBind_204_ = lean_ctor_get(v_inst_200_, 1);
lean_inc(v_toBind_204_);
lean_dec_ref(v_inst_200_);
v_toPure_205_ = lean_ctor_get(v_toApplicative_203_, 1);
lean_inc(v_toPure_205_);
lean_dec_ref(v_toApplicative_203_);
v___f_206_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_206_, 0, v_toPure_205_);
lean_closure_set(v___f_206_, 1, v_inst_201_);
lean_closure_set(v___f_206_, 2, v_toBind_204_);
lean_closure_set(v___f_206_, 3, v_inst_202_);
return v___f_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIterator(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b1_u2082_208_, lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Iterators_Types_Flatten_instIterator___redArg(v_inst_211_, v_inst_212_, v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b1_u2082_216_, lean_object* v_00_u03b2_217_, lean_object* v_m_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation___boxed(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b1_u2082_226_, lean_object* v_00_u03b2_227_, lean_object* v_m_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation(v_00_u03b1_225_, v_00_u03b1_u2082_226_, v_00_u03b2_227_, v_m_228_, v_inst_229_, v_inst_230_, v_inst_231_, v_inst_232_, v_inst_233_);
lean_dec(v_inst_231_);
lean_dec(v_inst_230_);
lean_dec_ref(v_inst_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b1_u2082_236_, lean_object* v_00_u03b2_237_, lean_object* v_m_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation___boxed(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b1_u2082_246_, lean_object* v_00_u03b2_247_, lean_object* v_m_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation(v_00_u03b1_245_, v_00_u03b1_u2082_246_, v_00_u03b2_247_, v_m_248_, v_inst_249_, v_inst_250_, v_inst_251_, v_inst_252_, v_inst_253_);
lean_dec(v_inst_251_);
lean_dec(v_inst_250_);
lean_dec_ref(v_inst_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_255_, lean_object* v_recur_256_, lean_object* v_it_257_, lean_object* v_____do__lift_258_){
_start:
{
if (lean_obj_tag(v_____do__lift_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_260_; 
lean_dec_ref(v_it_257_);
lean_dec(v_recur_256_);
v_a_259_ = lean_ctor_get(v_____do__lift_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref(v_____do__lift_258_);
v___x_260_ = lean_apply_2(v_toPure_255_, lean_box(0), v_a_259_);
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_toPure_255_);
v_a_261_ = lean_ctor_get(v_____do__lift_258_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v_____do__lift_258_);
v___x_262_ = lean_apply_4(v_recur_256_, v_it_257_, v_a_261_, lean_box(0), lean_box(0));
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_263_, lean_object* v_recur_264_, lean_object* v___y_265_, lean_object* v_acc_266_, lean_object* v_toBind_267_, lean_object* v_s_268_){
_start:
{
switch(lean_obj_tag(v_s_268_))
{
case 0:
{
lean_object* v_it_269_; lean_object* v_out_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_it_269_ = lean_ctor_get(v_s_268_, 0);
lean_inc(v_it_269_);
v_out_270_ = lean_ctor_get(v_s_268_, 1);
lean_inc(v_out_270_);
lean_dec_ref(v_s_268_);
v___f_271_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_271_, 0, v_toPure_263_);
lean_closure_set(v___f_271_, 1, v_recur_264_);
lean_closure_set(v___f_271_, 2, v_it_269_);
v___x_272_ = lean_apply_3(v___y_265_, v_out_270_, lean_box(0), v_acc_266_);
v___x_273_ = lean_apply_4(v_toBind_267_, lean_box(0), lean_box(0), v___x_272_, v___f_271_);
return v___x_273_;
}
case 1:
{
lean_object* v_it_274_; lean_object* v___x_275_; 
lean_dec(v_toBind_267_);
lean_dec(v___y_265_);
lean_dec(v_toPure_263_);
v_it_274_ = lean_ctor_get(v_s_268_, 0);
lean_inc(v_it_274_);
lean_dec_ref(v_s_268_);
v___x_275_ = lean_apply_4(v_recur_264_, v_it_274_, v_acc_266_, lean_box(0), lean_box(0));
return v___x_275_;
}
default: 
{
lean_object* v___x_276_; 
lean_dec(v_toBind_267_);
lean_dec(v___y_265_);
lean_dec(v_recur_264_);
v___x_276_ = lean_apply_2(v_toPure_263_, lean_box(0), v_acc_266_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__4(lean_object* v_inst_277_, lean_object* v_toPure_278_, lean_object* v___y_279_, lean_object* v_toBind_280_, lean_object* v_inst_281_, lean_object* v_lift_282_, lean_object* v_inst_283_, lean_object* v_it_284_, lean_object* v_acc_285_, lean_object* v_hP_286_, lean_object* v_recur_287_){
_start:
{
lean_object* v_toApplicative_288_; lean_object* v_toBind_289_; lean_object* v_toPure_290_; lean_object* v_it_u2081_291_; lean_object* v_it_u2082_292_; lean_object* v___f_293_; 
v_toApplicative_288_ = lean_ctor_get(v_inst_277_, 0);
lean_inc_ref(v_toApplicative_288_);
v_toBind_289_ = lean_ctor_get(v_inst_277_, 1);
lean_inc(v_toBind_289_);
lean_dec_ref(v_inst_277_);
v_toPure_290_ = lean_ctor_get(v_toApplicative_288_, 1);
lean_inc(v_toPure_290_);
lean_dec_ref(v_toApplicative_288_);
v_it_u2081_291_ = lean_ctor_get(v_it_284_, 0);
lean_inc(v_it_u2081_291_);
v_it_u2082_292_ = lean_ctor_get(v_it_284_, 1);
lean_inc(v_it_u2082_292_);
lean_dec_ref(v_it_284_);
v___f_293_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_293_, 0, v_toPure_278_);
lean_closure_set(v___f_293_, 1, v_recur_287_);
lean_closure_set(v___f_293_, 2, v___y_279_);
lean_closure_set(v___f_293_, 3, v_acc_285_);
lean_closure_set(v___f_293_, 4, v_toBind_280_);
if (lean_obj_tag(v_it_u2082_292_) == 0)
{
lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_inst_283_);
v___f_294_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0), 3, 2);
lean_closure_set(v___f_294_, 0, v_toPure_290_);
lean_closure_set(v___f_294_, 1, v_it_u2082_292_);
v___x_295_ = lean_apply_1(v_inst_281_, v_it_u2081_291_);
v___x_296_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v___x_295_, v___f_294_);
v___x_297_ = lean_apply_4(v_lift_282_, lean_box(0), lean_box(0), v___f_293_, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_val_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_inst_281_);
v_val_298_ = lean_ctor_get(v_it_u2082_292_, 0);
lean_inc(v_val_298_);
lean_dec_ref(v_it_u2082_292_);
v___f_299_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_299_, 0, v_it_u2081_291_);
lean_closure_set(v___f_299_, 1, v_toPure_290_);
v___x_300_ = lean_apply_1(v_inst_283_, v_val_298_);
v___x_301_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v___x_300_, v___f_299_);
v___x_302_ = lean_apply_4(v_lift_282_, lean_box(0), lean_box(0), v___f_293_, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_lift_307_, lean_object* v_00_u03b3_308_, lean_object* v_Pl_309_, lean_object* v_it_310_, lean_object* v_init_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_toApplicative_313_; lean_object* v_toBind_314_; lean_object* v_toPure_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
v_toApplicative_313_ = lean_ctor_get(v_inst_303_, 0);
lean_inc_ref(v_toApplicative_313_);
v_toBind_314_ = lean_ctor_get(v_inst_303_, 1);
lean_inc(v_toBind_314_);
lean_dec_ref(v_inst_303_);
v_toPure_315_ = lean_ctor_get(v_toApplicative_313_, 1);
lean_inc(v_toPure_315_);
lean_dec_ref(v_toApplicative_313_);
v___f_316_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_316_, 0, v_inst_304_);
lean_closure_set(v___f_316_, 1, v_toPure_315_);
lean_closure_set(v___f_316_, 2, v___y_312_);
lean_closure_set(v___f_316_, 3, v_toBind_314_);
lean_closure_set(v___f_316_, 4, v_inst_305_);
lean_closure_set(v___f_316_, 5, v_lift_307_);
lean_closure_set(v___f_316_, 6, v_inst_306_);
v___x_317_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_316_, v_it_310_, v_init_311_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg(lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_){
_start:
{
lean_object* v___f_322_; 
v___f_322_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_322_, 0, v_inst_319_);
lean_closure_set(v___f_322_, 1, v_inst_318_);
lean_closure_set(v___f_322_, 2, v_inst_320_);
lean_closure_set(v___f_322_, 3, v_inst_321_);
return v___f_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Flatten_instIteratorLoop(lean_object* v_00_u03b1_323_, lean_object* v_00_u03b1_u2082_324_, lean_object* v_00_u03b2_325_, lean_object* v_m_326_, lean_object* v_n_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_){
_start:
{
lean_object* v___f_332_; 
v___f_332_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_332_, 0, v_inst_329_);
lean_closure_set(v___f_332_, 1, v_inst_328_);
lean_closure_set(v___f_332_, 2, v_inst_330_);
lean_closure_set(v___f_332_, 3, v_inst_331_);
return v___f_332_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
}
#ifdef __cplusplus
}
#endif
