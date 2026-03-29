// Lean compiler output
// Module: Init.Data.String.Pattern.Pred
// Imports: public import Init.Data.String.Pattern.Basic public import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Termination import Init.Omega public import Init.Data.String.Basic import Init.Data.String.Lemmas.Order import Init.Data.Option.Lemmas import Init.Data.String.Lemmas.FindPos
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(lean_object* v_p_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_str_3_ = lean_ctor_get(v_s_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_s_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_s_2_, 2);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_sub(v_endExclusive_5_, v_startInclusive_4_);
v___x_8_ = lean_nat_dec_eq(v___x_6_, v___x_7_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
uint32_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_9_ = lean_string_utf8_get_fast(v_str_3_, v_startInclusive_4_);
v___x_10_ = lean_box_uint32(v___x_9_);
v___x_11_ = lean_apply_1(v_p_1_, v___x_10_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_string_utf8_next_fast(v_str_3_, v_startInclusive_4_);
v___x_15_ = lean_nat_sub(v___x_14_, v_startInclusive_4_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
else
{
lean_object* v___x_17_; 
lean_dec_ref(v_p_1_);
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed(lean_object* v_p_18_, lean_object* v_s_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(v_p_18_, v_s_19_);
lean_dec_ref(v_s_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(lean_object* v_p_21_, lean_object* v_s_22_, lean_object* v_h_23_){
_start:
{
lean_object* v_str_24_; lean_object* v_startInclusive_25_; uint32_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_str_24_ = lean_ctor_get(v_s_22_, 0);
v_startInclusive_25_ = lean_ctor_get(v_s_22_, 1);
v___x_26_ = lean_string_utf8_get_fast(v_str_24_, v_startInclusive_25_);
v___x_27_ = lean_box_uint32(v___x_26_);
v___x_28_ = lean_apply_1(v_p_21_, v___x_27_);
v___x_29_ = lean_unbox(v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_string_utf8_next_fast(v_str_24_, v_startInclusive_25_);
v___x_32_ = lean_nat_sub(v___x_31_, v_startInclusive_25_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed(lean_object* v_p_34_, lean_object* v_s_35_, lean_object* v_h_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(v_p_34_, v_s_35_, v_h_36_);
lean_dec_ref(v_s_35_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(lean_object* v_p_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_str_40_; lean_object* v_startInclusive_41_; lean_object* v_endExclusive_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_str_40_ = lean_ctor_get(v_s_39_, 0);
v_startInclusive_41_ = lean_ctor_get(v_s_39_, 1);
v_endExclusive_42_ = lean_ctor_get(v_s_39_, 2);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_sub(v_endExclusive_42_, v_startInclusive_41_);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_44_);
if (v___x_45_ == 0)
{
uint32_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_46_ = lean_string_utf8_get_fast(v_str_40_, v_startInclusive_41_);
v___x_47_ = lean_box_uint32(v___x_46_);
v___x_48_ = lean_apply_1(v_p_38_, v___x_47_);
v___x_49_ = lean_unbox(v___x_48_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
lean_dec_ref(v_p_38_);
v___x_50_ = 0;
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(lean_object* v_p_51_, lean_object* v_s_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(v_p_51_, v_s_52_);
lean_dec_ref(v_s_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object* v_p_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; 
lean_inc_ref_n(v_p_55_, 2);
v___f_56_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(v___f_56_, 0, v_p_55_);
v___f_57_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(v___f_57_, 0, v_p_55_);
v___f_58_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(v___f_58_, 0, v_p_55_);
v___x_59_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_59_, 0, v___f_56_);
lean_ctor_set(v___x_59_, 1, v___f_57_);
lean_ctor_set(v___x_59_, 2, v___f_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(lean_object* v_p_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, v_p_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* v_inst_62_, lean_object* v_s_63_){
_start:
{
lean_object* v_str_64_; lean_object* v_startInclusive_65_; lean_object* v_endExclusive_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_str_64_ = lean_ctor_get(v_s_63_, 0);
v_startInclusive_65_ = lean_ctor_get(v_s_63_, 1);
v_endExclusive_66_ = lean_ctor_get(v_s_63_, 2);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_sub(v_endExclusive_66_, v_startInclusive_65_);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
lean_dec(v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_70_ = lean_string_utf8_get_fast(v_str_64_, v_startInclusive_65_);
v___x_71_ = lean_box_uint32(v___x_70_);
v___x_72_ = lean_apply_1(v_inst_62_, v___x_71_);
v___x_73_ = lean_unbox(v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_string_utf8_next_fast(v_str_64_, v_startInclusive_65_);
v___x_76_ = lean_nat_sub(v___x_75_, v_startInclusive_65_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
else
{
lean_object* v___x_78_; 
lean_dec_ref(v_inst_62_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* v_inst_79_, lean_object* v_s_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_79_, v_s_80_);
lean_dec_ref(v_s_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* v_inst_82_, lean_object* v_s_83_, lean_object* v_h_84_){
_start:
{
lean_object* v_str_85_; lean_object* v_startInclusive_86_; uint32_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_str_85_ = lean_ctor_get(v_s_83_, 0);
v_startInclusive_86_ = lean_ctor_get(v_s_83_, 1);
v___x_87_ = lean_string_utf8_get_fast(v_str_85_, v_startInclusive_86_);
v___x_88_ = lean_box_uint32(v___x_87_);
v___x_89_ = lean_apply_1(v_inst_82_, v___x_88_);
v___x_90_ = lean_unbox(v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_string_utf8_next_fast(v_str_85_, v_startInclusive_86_);
v___x_93_ = lean_nat_sub(v___x_92_, v_startInclusive_86_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* v_inst_95_, lean_object* v_s_96_, lean_object* v_h_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_95_, v_s_96_, v_h_97_);
lean_dec_ref(v_s_96_);
return v_res_98_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* v_inst_99_, lean_object* v_s_100_){
_start:
{
lean_object* v_str_101_; lean_object* v_startInclusive_102_; lean_object* v_endExclusive_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_str_101_ = lean_ctor_get(v_s_100_, 0);
v_startInclusive_102_ = lean_ctor_get(v_s_100_, 1);
v_endExclusive_103_ = lean_ctor_get(v_s_100_, 2);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_sub(v_endExclusive_103_, v_startInclusive_102_);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
lean_dec(v___x_105_);
if (v___x_106_ == 0)
{
uint32_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_107_ = lean_string_utf8_get_fast(v_str_101_, v_startInclusive_102_);
v___x_108_ = lean_box_uint32(v___x_107_);
v___x_109_ = lean_apply_1(v_inst_99_, v___x_108_);
v___x_110_ = lean_unbox(v___x_109_);
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
lean_dec_ref(v_inst_99_);
v___x_111_ = 0;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* v_inst_112_, lean_object* v_s_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_112_, v_s_113_);
lean_dec_ref(v_s_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(lean_object* v_inst_116_){
_start:
{
lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
lean_inc_ref_n(v_inst_116_, 2);
v___f_117_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_117_, 0, v_inst_116_);
v___f_118_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_118_, 0, v_inst_116_);
v___f_119_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v_inst_116_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___f_117_);
lean_ctor_set(v___x_120_, 1, v___f_118_);
lean_ctor_set(v___x_120_, 2, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred(lean_object* v_p_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(v_inst_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0(lean_object* v_s_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(0u);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0___boxed(lean_object* v_s_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0(v_s_126_);
lean_dec_ref(v_s_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(lean_object* v_p_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0));
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___boxed(lean_object* v_p_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(v_p_132_, v_inst_133_);
lean_dec_ref(v_inst_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(lean_object* v_p_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_str_137_; lean_object* v_startInclusive_138_; lean_object* v_endExclusive_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_str_137_ = lean_ctor_get(v_s_136_, 0);
v_startInclusive_138_ = lean_ctor_get(v_s_136_, 1);
v_endExclusive_139_ = lean_ctor_get(v_s_136_, 2);
v___x_140_ = lean_nat_sub(v_endExclusive_139_, v_startInclusive_138_);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint32_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_sub(v___x_140_, v___x_143_);
lean_dec(v___x_140_);
v___x_145_ = l_String_Slice_posLE(v_s_136_, v___x_144_);
v___x_146_ = lean_nat_add(v_startInclusive_138_, v___x_145_);
v___x_147_ = lean_string_utf8_get_fast(v_str_137_, v___x_146_);
lean_dec(v___x_146_);
v___x_148_ = lean_box_uint32(v___x_147_);
v___x_149_ = lean_apply_1(v_p_135_, v___x_148_);
v___x_150_ = lean_unbox(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v___x_145_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_145_);
return v___x_152_;
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_140_);
lean_dec_ref(v_p_135_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(lean_object* v_p_154_, lean_object* v_s_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(v_p_154_, v_s_155_);
lean_dec_ref(v_s_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(lean_object* v_p_157_, lean_object* v_s_158_, lean_object* v_h_159_){
_start:
{
lean_object* v_str_160_; lean_object* v_startInclusive_161_; lean_object* v_endExclusive_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint32_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_str_160_ = lean_ctor_get(v_s_158_, 0);
v_startInclusive_161_ = lean_ctor_get(v_s_158_, 1);
v_endExclusive_162_ = lean_ctor_get(v_s_158_, 2);
v___x_163_ = lean_nat_sub(v_endExclusive_162_, v_startInclusive_161_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_sub(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_166_ = l_String_Slice_posLE(v_s_158_, v___x_165_);
v___x_167_ = lean_nat_add(v_startInclusive_161_, v___x_166_);
v___x_168_ = lean_string_utf8_get_fast(v_str_160_, v___x_167_);
lean_dec(v___x_167_);
v___x_169_ = lean_box_uint32(v___x_168_);
v___x_170_ = lean_apply_1(v_p_157_, v___x_169_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
lean_dec(v___x_166_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_166_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(lean_object* v_p_174_, lean_object* v_s_175_, lean_object* v_h_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(v_p_174_, v_s_175_, v_h_176_);
lean_dec_ref(v_s_175_);
return v_res_177_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(lean_object* v_p_178_, lean_object* v_s_179_){
_start:
{
lean_object* v_str_180_; lean_object* v_startInclusive_181_; lean_object* v_endExclusive_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_str_180_ = lean_ctor_get(v_s_179_, 0);
v_startInclusive_181_ = lean_ctor_get(v_s_179_, 1);
v_endExclusive_182_ = lean_ctor_get(v_s_179_, 2);
v___x_183_ = lean_nat_sub(v_endExclusive_182_, v_startInclusive_181_);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_nat_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint32_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_sub(v___x_183_, v___x_186_);
lean_dec(v___x_183_);
v___x_188_ = l_String_Slice_posLE(v_s_179_, v___x_187_);
v___x_189_ = lean_nat_add(v_startInclusive_181_, v___x_188_);
lean_dec(v___x_188_);
v___x_190_ = lean_string_utf8_get_fast(v_str_180_, v___x_189_);
lean_dec(v___x_189_);
v___x_191_ = lean_box_uint32(v___x_190_);
v___x_192_ = lean_apply_1(v_p_178_, v___x_191_);
v___x_193_ = lean_unbox(v___x_192_);
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
lean_dec(v___x_183_);
lean_dec_ref(v_p_178_);
v___x_194_ = 0;
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(lean_object* v_p_195_, lean_object* v_s_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(v_p_195_, v_s_196_);
lean_dec_ref(v_s_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object* v_p_199_){
_start:
{
lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
lean_inc_ref_n(v_p_199_, 2);
v___f_200_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(v___f_200_, 0, v_p_199_);
v___f_201_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(v___f_201_, 0, v_p_199_);
v___f_202_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(v___f_202_, 0, v_p_199_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v___f_200_);
lean_ctor_set(v___x_203_, 1, v___f_201_);
lean_ctor_set(v___x_203_, 2, v___f_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(lean_object* v_p_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, v_p_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* v_inst_206_, lean_object* v_s_207_){
_start:
{
lean_object* v_str_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_str_208_ = lean_ctor_get(v_s_207_, 0);
v_startInclusive_209_ = lean_ctor_get(v_s_207_, 1);
v_endExclusive_210_ = lean_ctor_get(v_s_207_, 2);
v___x_211_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_nat_dec_eq(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint32_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_sub(v___x_211_, v___x_214_);
lean_dec(v___x_211_);
v___x_216_ = l_String_Slice_posLE(v_s_207_, v___x_215_);
v___x_217_ = lean_nat_add(v_startInclusive_209_, v___x_216_);
v___x_218_ = lean_string_utf8_get_fast(v_str_208_, v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = lean_box_uint32(v___x_218_);
v___x_220_ = lean_apply_1(v_inst_206_, v___x_219_);
v___x_221_ = lean_unbox(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v___x_216_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_216_);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v___x_211_);
lean_dec_ref(v_inst_206_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* v_inst_225_, lean_object* v_s_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_225_, v_s_226_);
lean_dec_ref(v_s_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* v_inst_228_, lean_object* v_s_229_, lean_object* v_h_230_){
_start:
{
lean_object* v_str_231_; lean_object* v_startInclusive_232_; lean_object* v_endExclusive_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint32_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_str_231_ = lean_ctor_get(v_s_229_, 0);
v_startInclusive_232_ = lean_ctor_get(v_s_229_, 1);
v_endExclusive_233_ = lean_ctor_get(v_s_229_, 2);
v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_sub(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
v___x_237_ = l_String_Slice_posLE(v_s_229_, v___x_236_);
v___x_238_ = lean_nat_add(v_startInclusive_232_, v___x_237_);
v___x_239_ = lean_string_utf8_get_fast(v_str_231_, v___x_238_);
lean_dec(v___x_238_);
v___x_240_ = lean_box_uint32(v___x_239_);
v___x_241_ = lean_apply_1(v_inst_228_, v___x_240_);
v___x_242_ = lean_unbox(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v___x_237_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_237_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* v_inst_245_, lean_object* v_s_246_, lean_object* v_h_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_245_, v_s_246_, v_h_247_);
lean_dec_ref(v_s_246_);
return v_res_248_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* v_inst_249_, lean_object* v_s_250_){
_start:
{
lean_object* v_str_251_; lean_object* v_startInclusive_252_; lean_object* v_endExclusive_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_str_251_ = lean_ctor_get(v_s_250_, 0);
v_startInclusive_252_ = lean_ctor_get(v_s_250_, 1);
v_endExclusive_253_ = lean_ctor_get(v_s_250_, 2);
v___x_254_ = lean_nat_sub(v_endExclusive_253_, v_startInclusive_252_);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_nat_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint32_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_sub(v___x_254_, v___x_257_);
lean_dec(v___x_254_);
v___x_259_ = l_String_Slice_posLE(v_s_250_, v___x_258_);
v___x_260_ = lean_nat_add(v_startInclusive_252_, v___x_259_);
lean_dec(v___x_259_);
v___x_261_ = lean_string_utf8_get_fast(v_str_251_, v___x_260_);
lean_dec(v___x_260_);
v___x_262_ = lean_box_uint32(v___x_261_);
v___x_263_ = lean_apply_1(v_inst_249_, v___x_262_);
v___x_264_ = lean_unbox(v___x_263_);
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
lean_dec(v___x_254_);
lean_dec_ref(v_inst_249_);
v___x_265_ = 0;
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* v_inst_266_, lean_object* v_s_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_266_, v_s_267_);
lean_dec_ref(v_s_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(lean_object* v_inst_270_){
_start:
{
lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___x_274_; 
lean_inc_ref_n(v_inst_270_, 2);
v___f_271_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_271_, 0, v_inst_270_);
v___f_272_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_272_, 0, v_inst_270_);
v___f_273_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_273_, 0, v_inst_270_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v___f_271_);
lean_ctor_set(v___x_274_, 1, v___f_272_);
lean_ctor_set(v___x_274_, 2, v___f_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred(lean_object* v_p_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(v_inst_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0(lean_object* v_s_278_){
_start:
{
lean_object* v_startInclusive_279_; lean_object* v_endExclusive_280_; lean_object* v___x_281_; 
v_startInclusive_279_ = lean_ctor_get(v_s_278_, 1);
v_endExclusive_280_ = lean_ctor_get(v_s_278_, 2);
v___x_281_ = lean_nat_sub(v_endExclusive_280_, v_startInclusive_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0___boxed(lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0(v_s_282_);
lean_dec_ref(v_s_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(lean_object* v_p_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0));
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___boxed(lean_object* v_p_288_, lean_object* v_inst_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(v_p_288_, v_inst_289_);
lean_dec_ref(v_inst_289_);
return v_res_290_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Pattern_Pred(builtin);
}
#ifdef __cplusplus
}
#endif
