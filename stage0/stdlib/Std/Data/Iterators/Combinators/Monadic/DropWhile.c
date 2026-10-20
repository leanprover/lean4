// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.DropWhile
// Imports: public import Init.Data.Nat.Lemmas public import Init.Data.Iterators.Consumers.Monadic.Collect public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Data.Iterators.PostconditionMonad
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
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(uint8_t v_dropping_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3_, 0, v_it_2_);
lean_ctor_set_uint8(v___x_3_, sizeof(void*)*1, v_dropping_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(lean_object* v_dropping_4_, lean_object* v_it_5_){
_start:
{
uint8_t v_dropping_boxed_6_; lean_object* v_res_7_; 
v_dropping_boxed_6_ = lean_unbox(v_dropping_4_);
v_res_7_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(v_dropping_boxed_6_, v_it_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition(lean_object* v_00_u03b1_8_, lean_object* v_m_9_, lean_object* v_00_u03b2_10_, lean_object* v_P_11_, uint8_t v_dropping_12_, lean_object* v_it_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_14_, 0, v_it_13_);
lean_ctor_set_uint8(v___x_14_, sizeof(void*)*1, v_dropping_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(lean_object* v_00_u03b1_15_, lean_object* v_m_16_, lean_object* v_00_u03b2_17_, lean_object* v_P_18_, lean_object* v_dropping_19_, lean_object* v_it_20_){
_start:
{
uint8_t v_dropping_boxed_21_; lean_object* v_res_22_; 
v_dropping_boxed_21_ = lean_unbox(v_dropping_19_);
v_res_22_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition(v_00_u03b1_15_, v_m_16_, v_00_u03b2_17_, v_P_18_, v_dropping_boxed_21_, v_it_20_);
lean_dec(v_P_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg(uint8_t v_dropping_23_, lean_object* v_it_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_25_, 0, v_it_24_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v_dropping_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(lean_object* v_dropping_26_, lean_object* v_it_27_){
_start:
{
uint8_t v_dropping_boxed_28_; lean_object* v_res_29_; 
v_dropping_boxed_28_ = lean_unbox(v_dropping_26_);
v_res_29_ = l_Std_IterM_Intermediate_dropWhileM___redArg(v_dropping_boxed_28_, v_it_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM(lean_object* v_00_u03b1_30_, lean_object* v_m_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_P_35_, uint8_t v_dropping_36_, lean_object* v_it_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_38_, 0, v_it_37_);
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*1, v_dropping_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhileM___boxed(lean_object* v_00_u03b1_39_, lean_object* v_m_40_, lean_object* v_00_u03b2_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_P_44_, lean_object* v_dropping_45_, lean_object* v_it_46_){
_start:
{
uint8_t v_dropping_boxed_47_; lean_object* v_res_48_; 
v_dropping_boxed_47_ = lean_unbox(v_dropping_45_);
v_res_48_ = l_Std_IterM_Intermediate_dropWhileM(v_00_u03b1_39_, v_m_40_, v_00_u03b2_41_, v_inst_42_, v_inst_43_, v_P_44_, v_dropping_boxed_47_, v_it_46_);
lean_dec(v_P_44_);
lean_dec(v_inst_43_);
lean_dec_ref(v_inst_42_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg(uint8_t v_dropping_49_, lean_object* v_it_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_51_, 0, v_it_50_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v_dropping_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___redArg___boxed(lean_object* v_dropping_52_, lean_object* v_it_53_){
_start:
{
uint8_t v_dropping_boxed_54_; lean_object* v_res_55_; 
v_dropping_boxed_54_ = lean_unbox(v_dropping_52_);
v_res_55_ = l_Std_IterM_Intermediate_dropWhile___redArg(v_dropping_boxed_54_, v_it_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile(lean_object* v_00_u03b1_56_, lean_object* v_m_57_, lean_object* v_00_u03b2_58_, lean_object* v_inst_59_, lean_object* v_P_60_, uint8_t v_dropping_61_, lean_object* v_it_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_63_, 0, v_it_62_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*1, v_dropping_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Intermediate_dropWhile___boxed(lean_object* v_00_u03b1_64_, lean_object* v_m_65_, lean_object* v_00_u03b2_66_, lean_object* v_inst_67_, lean_object* v_P_68_, lean_object* v_dropping_69_, lean_object* v_it_70_){
_start:
{
uint8_t v_dropping_boxed_71_; lean_object* v_res_72_; 
v_dropping_boxed_71_ = lean_unbox(v_dropping_69_);
v_res_72_ = l_Std_IterM_Intermediate_dropWhile(v_00_u03b1_64_, v_m_65_, v_00_u03b2_66_, v_inst_67_, v_P_68_, v_dropping_boxed_71_, v_it_70_);
lean_dec_ref(v_P_68_);
lean_dec_ref(v_inst_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___redArg(lean_object* v_it_73_){
_start:
{
uint8_t v___x_74_; lean_object* v___x_75_; 
v___x_74_ = 1;
v___x_75_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_75_, 0, v_it_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition(lean_object* v_00_u03b1_76_, lean_object* v_m_77_, lean_object* v_00_u03b2_78_, lean_object* v_P_79_, lean_object* v_it_80_){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 1;
v___x_82_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_82_, 0, v_it_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileWithPostcondition___boxed(lean_object* v_00_u03b1_83_, lean_object* v_m_84_, lean_object* v_00_u03b2_85_, lean_object* v_P_86_, lean_object* v_it_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_IterM_dropWhileWithPostcondition(v_00_u03b1_83_, v_m_84_, v_00_u03b2_85_, v_P_86_, v_it_87_);
lean_dec(v_P_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___redArg(lean_object* v_it_89_){
_start:
{
uint8_t v___x_90_; lean_object* v___x_91_; 
v___x_90_ = 1;
v___x_91_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_91_, 0, v_it_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM(lean_object* v_00_u03b1_92_, lean_object* v_m_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_P_97_, lean_object* v_it_98_){
_start:
{
uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_99_ = 1;
v___x_100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_100_, 0, v_it_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhileM___boxed(lean_object* v_00_u03b1_101_, lean_object* v_m_102_, lean_object* v_00_u03b2_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_P_106_, lean_object* v_it_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_IterM_dropWhileM(v_00_u03b1_101_, v_m_102_, v_00_u03b2_103_, v_inst_104_, v_inst_105_, v_P_106_, v_it_107_);
lean_dec(v_P_106_);
lean_dec(v_inst_105_);
lean_dec_ref(v_inst_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___redArg(lean_object* v_it_109_){
_start:
{
uint8_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = 1;
v___x_111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_111_, 0, v_it_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile(lean_object* v_00_u03b1_112_, lean_object* v_m_113_, lean_object* v_00_u03b2_114_, lean_object* v_inst_115_, lean_object* v_P_116_, lean_object* v_it_117_){
_start:
{
uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = 1;
v___x_119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_119_, 0, v_it_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_dropWhile___boxed(lean_object* v_00_u03b1_120_, lean_object* v_m_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_P_124_, lean_object* v_it_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_IterM_dropWhile(v_00_u03b1_120_, v_m_121_, v_00_u03b2_122_, v_inst_123_, v_P_124_, v_it_125_);
lean_dec_ref(v_P_124_);
lean_dec_ref(v_inst_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(lean_object* v_it_127_, lean_object* v_out_128_, lean_object* v_toPure_129_, uint8_t v_dropping_130_, uint8_t v_____do__lift_131_){
_start:
{
if (v_____do__lift_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_132_, 0, v_it_127_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v_____do__lift_131_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_out_128_);
v___x_134_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_out_128_);
v___x_135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_135_, 0, v_it_127_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v_dropping_130_);
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
v___x_137_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(lean_object* v_it_138_, lean_object* v_out_139_, lean_object* v_toPure_140_, lean_object* v_dropping_141_, lean_object* v_____do__lift_142_){
_start:
{
uint8_t v_dropping_boxed_143_; uint8_t v_____do__lift_247__boxed_144_; lean_object* v_res_145_; 
v_dropping_boxed_143_ = lean_unbox(v_dropping_141_);
v_____do__lift_247__boxed_144_ = lean_unbox(v_____do__lift_142_);
v_res_145_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(v_it_138_, v_out_139_, v_toPure_140_, v_dropping_boxed_143_, v_____do__lift_247__boxed_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(uint8_t v_dropping_146_, lean_object* v_toPure_147_, lean_object* v_P_148_, lean_object* v_toBind_149_, lean_object* v_____do__lift_150_){
_start:
{
switch(lean_obj_tag(v_____do__lift_150_))
{
case 0:
{
if (v_dropping_146_ == 0)
{
lean_object* v_it_151_; lean_object* v_out_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_toBind_149_);
lean_dec(v_P_148_);
v_it_151_ = lean_ctor_get(v_____do__lift_150_, 0);
v_out_152_ = lean_ctor_get(v_____do__lift_150_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_____do__lift_150_);
if (v_isSharedCheck_161_ == 0)
{
v___x_154_ = v_____do__lift_150_;
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_out_152_);
lean_inc(v_it_151_);
lean_dec(v_____do__lift_150_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_156_, 0, v_it_151_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v_dropping_146_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_out_152_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_apply_2(v_toPure_147_, lean_box(0), v___x_158_);
return v___x_159_;
}
}
}
else
{
lean_object* v_it_162_; lean_object* v_out_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_it_162_ = lean_ctor_get(v_____do__lift_150_, 0);
lean_inc(v_it_162_);
v_out_163_ = lean_ctor_get(v_____do__lift_150_, 1);
lean_inc_n(v_out_163_, 2);
lean_dec_ref_known(v_____do__lift_150_, 2);
v___x_164_ = lean_box(v_dropping_146_);
v___f_165_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_165_, 0, v_it_162_);
lean_closure_set(v___f_165_, 1, v_out_163_);
lean_closure_set(v___f_165_, 2, v_toPure_147_);
lean_closure_set(v___f_165_, 3, v___x_164_);
v___x_166_ = lean_apply_1(v_P_148_, v_out_163_);
v___x_167_ = lean_apply_4(v_toBind_149_, lean_box(0), lean_box(0), v___x_166_, v___f_165_);
return v___x_167_;
}
}
case 1:
{
lean_object* v_it_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_toBind_149_);
lean_dec(v_P_148_);
v_it_168_ = lean_ctor_get(v_____do__lift_150_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v_____do__lift_150_);
if (v_isSharedCheck_177_ == 0)
{
v___x_170_ = v_____do__lift_150_;
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_it_168_);
lean_dec(v_____do__lift_150_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_172_, 0, v_it_168_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v_dropping_146_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_176_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; 
v___x_175_ = lean_apply_2(v_toPure_147_, lean_box(0), v___x_174_);
return v___x_175_;
}
}
}
default: 
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_toBind_149_);
lean_dec(v_P_148_);
v___x_178_ = lean_box(2);
v___x_179_ = lean_apply_2(v_toPure_147_, lean_box(0), v___x_178_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(lean_object* v_dropping_180_, lean_object* v_toPure_181_, lean_object* v_P_182_, lean_object* v_toBind_183_, lean_object* v_____do__lift_184_){
_start:
{
uint8_t v_dropping_boxed_185_; lean_object* v_res_186_; 
v_dropping_boxed_185_ = lean_unbox(v_dropping_180_);
v_res_186_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(v_dropping_boxed_185_, v_toPure_181_, v_P_182_, v_toBind_183_, v_____do__lift_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2(lean_object* v_toPure_187_, lean_object* v_P_188_, lean_object* v_toBind_189_, lean_object* v_inst_190_, lean_object* v_it_191_){
_start:
{
uint8_t v_dropping_192_; lean_object* v_inner_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_dropping_192_ = lean_ctor_get_uint8(v_it_191_, sizeof(void*)*1);
v_inner_193_ = lean_ctor_get(v_it_191_, 0);
lean_inc(v_inner_193_);
lean_dec_ref(v_it_191_);
v___x_194_ = lean_box(v_dropping_192_);
lean_inc(v_toBind_189_);
v___f_195_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_195_, 0, v___x_194_);
lean_closure_set(v___f_195_, 1, v_toPure_187_);
lean_closure_set(v___f_195_, 2, v_P_188_);
lean_closure_set(v___f_195_, 3, v_toBind_189_);
v___x_196_ = lean_apply_1(v_inst_190_, v_inner_193_);
v___x_197_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v___x_196_, v___f_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator___redArg(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_P_200_){
_start:
{
lean_object* v_toApplicative_201_; lean_object* v_toBind_202_; lean_object* v_toPure_203_; lean_object* v___f_204_; 
v_toApplicative_201_ = lean_ctor_get(v_inst_198_, 0);
lean_inc_ref(v_toApplicative_201_);
v_toBind_202_ = lean_ctor_get(v_inst_198_, 1);
lean_inc(v_toBind_202_);
lean_dec_ref(v_inst_198_);
v_toPure_203_ = lean_ctor_get(v_toApplicative_201_, 1);
lean_inc(v_toPure_203_);
lean_dec_ref(v_toApplicative_201_);
v___f_204_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_204_, 0, v_toPure_203_);
lean_closure_set(v___f_204_, 1, v_P_200_);
lean_closure_set(v___f_204_, 2, v_toBind_202_);
lean_closure_set(v___f_204_, 3, v_inst_199_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIterator(lean_object* v_00_u03b1_205_, lean_object* v_m_206_, lean_object* v_00_u03b2_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_P_210_){
_start:
{
lean_object* v_toApplicative_211_; lean_object* v_toBind_212_; lean_object* v_toPure_213_; lean_object* v___f_214_; 
v_toApplicative_211_ = lean_ctor_get(v_inst_208_, 0);
lean_inc_ref(v_toApplicative_211_);
v_toBind_212_ = lean_ctor_get(v_inst_208_, 1);
lean_inc(v_toBind_212_);
lean_dec_ref(v_inst_208_);
v_toPure_213_ = lean_ctor_get(v_toApplicative_211_, 1);
lean_inc(v_toPure_213_);
lean_dec_ref(v_toApplicative_211_);
v___f_214_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_214_, 0, v_toPure_213_);
lean_closure_set(v___f_214_, 1, v_P_210_);
lean_closure_set(v___f_214_, 2, v_toBind_212_);
lean_closure_set(v___f_214_, 3, v_inst_209_);
return v___f_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___redArg();
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(lean_object* v_00_u03b1_219_, lean_object* v_m_220_, lean_object* v_00_u03b2_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_P_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(lean_object* v_00_u03b1_227_, lean_object* v_m_228_, lean_object* v_00_u03b2_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_P_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(v_00_u03b1_227_, v_m_228_, v_00_u03b2_229_, v_inst_230_, v_inst_231_, v_inst_232_, v_P_233_);
lean_dec(v_P_233_);
lean_dec(v_inst_231_);
lean_dec_ref(v_inst_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_235_, lean_object* v_recur_236_, lean_object* v_it_237_, lean_object* v_____do__lift_238_){
_start:
{
if (lean_obj_tag(v_____do__lift_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; 
lean_dec_ref(v_it_237_);
lean_dec(v_recur_236_);
v_a_239_ = lean_ctor_get(v_____do__lift_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v_____do__lift_238_, 1);
v___x_240_ = lean_apply_2(v_toPure_235_, lean_box(0), v_a_239_);
return v___x_240_;
}
else
{
lean_object* v_a_241_; lean_object* v___x_242_; 
lean_dec(v_toPure_235_);
v_a_241_ = lean_ctor_get(v_____do__lift_238_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v_____do__lift_238_, 1);
v___x_242_ = lean_apply_4(v_recur_236_, v_it_237_, v_a_241_, lean_box(0), lean_box(0));
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_243_, lean_object* v_recur_244_, lean_object* v___y_245_, lean_object* v_acc_246_, lean_object* v_toBind_247_, lean_object* v_s_248_){
_start:
{
switch(lean_obj_tag(v_s_248_))
{
case 0:
{
lean_object* v_it_249_; lean_object* v_out_250_; lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_it_249_ = lean_ctor_get(v_s_248_, 0);
lean_inc(v_it_249_);
v_out_250_ = lean_ctor_get(v_s_248_, 1);
lean_inc(v_out_250_);
lean_dec_ref_known(v_s_248_, 2);
v___f_251_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_251_, 0, v_toPure_243_);
lean_closure_set(v___f_251_, 1, v_recur_244_);
lean_closure_set(v___f_251_, 2, v_it_249_);
v___x_252_ = lean_apply_3(v___y_245_, v_out_250_, lean_box(0), v_acc_246_);
v___x_253_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_252_, v___f_251_);
return v___x_253_;
}
case 1:
{
lean_object* v_it_254_; lean_object* v___x_255_; 
lean_dec(v_toBind_247_);
lean_dec(v___y_245_);
lean_dec(v_toPure_243_);
v_it_254_ = lean_ctor_get(v_s_248_, 0);
lean_inc(v_it_254_);
lean_dec_ref_known(v_s_248_, 1);
v___x_255_ = lean_apply_4(v_recur_244_, v_it_254_, v_acc_246_, lean_box(0), lean_box(0));
return v___x_255_;
}
default: 
{
lean_object* v___x_256_; 
lean_dec(v_toBind_247_);
lean_dec(v___y_245_);
lean_dec(v_recur_244_);
v___x_256_ = lean_apply_2(v_toPure_243_, lean_box(0), v_acc_246_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(lean_object* v_inst_257_, lean_object* v_toPure_258_, lean_object* v___y_259_, lean_object* v_toBind_260_, lean_object* v_P_261_, lean_object* v_inst_262_, lean_object* v_lift_263_, lean_object* v_it_264_, lean_object* v_acc_265_, lean_object* v_hP_266_, lean_object* v_recur_267_){
_start:
{
lean_object* v_toApplicative_268_; lean_object* v_toBind_269_; lean_object* v_toPure_270_; uint8_t v_dropping_271_; lean_object* v_inner_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_toApplicative_268_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_268_);
v_toBind_269_ = lean_ctor_get(v_inst_257_, 1);
lean_inc_n(v_toBind_269_, 2);
lean_dec_ref(v_inst_257_);
v_toPure_270_ = lean_ctor_get(v_toApplicative_268_, 1);
lean_inc(v_toPure_270_);
lean_dec_ref(v_toApplicative_268_);
v_dropping_271_ = lean_ctor_get_uint8(v_it_264_, sizeof(void*)*1);
v_inner_272_ = lean_ctor_get(v_it_264_, 0);
lean_inc(v_inner_272_);
lean_dec_ref(v_it_264_);
v___f_273_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_273_, 0, v_toPure_258_);
lean_closure_set(v___f_273_, 1, v_recur_267_);
lean_closure_set(v___f_273_, 2, v___y_259_);
lean_closure_set(v___f_273_, 3, v_acc_265_);
lean_closure_set(v___f_273_, 4, v_toBind_260_);
v___x_274_ = lean_box(v_dropping_271_);
v___f_275_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_275_, 0, v___x_274_);
lean_closure_set(v___f_275_, 1, v_toPure_270_);
lean_closure_set(v___f_275_, 2, v_P_261_);
lean_closure_set(v___f_275_, 3, v_toBind_269_);
v___x_276_ = lean_apply_1(v_inst_262_, v_inner_272_);
v___x_277_ = lean_apply_4(v_toBind_269_, lean_box(0), lean_box(0), v___x_276_, v___f_275_);
v___x_278_ = lean_apply_4(v_lift_263_, lean_box(0), lean_box(0), v___f_273_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_P_281_, lean_object* v_inst_282_, lean_object* v_lift_283_, lean_object* v_00_u03b3_284_, lean_object* v_Pl_285_, lean_object* v_it_286_, lean_object* v_init_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_toApplicative_289_; lean_object* v_toBind_290_; lean_object* v_toPure_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_toApplicative_289_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_toApplicative_289_);
v_toBind_290_ = lean_ctor_get(v_inst_279_, 1);
lean_inc(v_toBind_290_);
lean_dec_ref(v_inst_279_);
v_toPure_291_ = lean_ctor_get(v_toApplicative_289_, 1);
lean_inc(v_toPure_291_);
lean_dec_ref(v_toApplicative_289_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_292_, 0, v_inst_280_);
lean_closure_set(v___f_292_, 1, v_toPure_291_);
lean_closure_set(v___f_292_, 2, v___y_288_);
lean_closure_set(v___f_292_, 3, v_toBind_290_);
lean_closure_set(v___f_292_, 4, v_P_281_);
lean_closure_set(v___f_292_, 5, v_inst_282_);
lean_closure_set(v___f_292_, 6, v_lift_283_);
v___x_293_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_292_, v_it_286_, v_init_287_, lean_box(0));
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(lean_object* v_P_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_){
_start:
{
lean_object* v___f_298_; 
v___f_298_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_298_, 0, v_inst_296_);
lean_closure_set(v___f_298_, 1, v_inst_295_);
lean_closure_set(v___f_298_, 2, v_P_294_);
lean_closure_set(v___f_298_, 3, v_inst_297_);
return v___f_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_DropWhile_instIteratorLoop(lean_object* v_00_u03b1_299_, lean_object* v_m_300_, lean_object* v_00_u03b2_301_, lean_object* v_n_302_, lean_object* v_P_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_){
_start:
{
lean_object* v___f_307_; 
v___f_307_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_307_, 0, v_inst_305_);
lean_closure_set(v___f_307_, 1, v_inst_304_);
lean_closure_set(v___f_307_, 2, v_P_303_);
lean_closure_set(v___f_307_, 3, v_inst_306_);
return v___f_307_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
}
#ifdef __cplusplus
}
#endif
