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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___closed__0 = (const lean_object*)&l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg();
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(lean_object* v_p_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v_decide_8_; 
v_str_3_ = lean_ctor_get(v_s_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_s_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_s_2_, 2);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_sub(v_endExclusive_5_, v_startInclusive_4_);
v_decide_8_ = lean_nat_dec_eq(v___x_6_, v___x_7_);
lean_dec(v___x_7_);
if (v_decide_8_ == 0)
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
uint8_t l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(lean_object* v_p_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_str_40_; lean_object* v_startInclusive_41_; lean_object* v_endExclusive_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v_decide_45_; 
v_str_40_ = lean_ctor_get(v_s_39_, 0);
v_startInclusive_41_ = lean_ctor_get(v_s_39_, 1);
v_endExclusive_42_ = lean_ctor_get(v_s_39_, 2);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_sub(v_endExclusive_42_, v_startInclusive_41_);
v_decide_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_44_);
if (v_decide_45_ == 0)
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
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_38_ = stack[0].m_obj;
lean_object* v_s_39_ = stack[1].m_obj;
uint8_t v_res_51_;
v_res_51_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(v_p_38_, v_s_39_);
stack->m_num = v_res_51_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(lean_object* v_p_52_, lean_object* v_s_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(v_p_52_, v_s_53_);
lean_dec_ref(v_s_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object* v_p_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; 
lean_inc_ref_n(v_p_56_, 2);
v___f_57_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(v___f_57_, 0, v_p_56_);
v___f_58_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(v___f_58_, 0, v_p_56_);
v___f_59_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(v___f_59_, 0, v_p_56_);
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v___f_57_);
lean_ctor_set(v___x_60_, 1, v___f_58_);
lean_ctor_set(v___x_60_, 2, v___f_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(lean_object* v_p_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, v_p_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* v_inst_63_, lean_object* v_s_64_){
_start:
{
lean_object* v_str_65_; lean_object* v_startInclusive_66_; lean_object* v_endExclusive_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v_decide_70_; 
v_str_65_ = lean_ctor_get(v_s_64_, 0);
v_startInclusive_66_ = lean_ctor_get(v_s_64_, 1);
v_endExclusive_67_ = lean_ctor_get(v_s_64_, 2);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_sub(v_endExclusive_67_, v_startInclusive_66_);
v_decide_70_ = lean_nat_dec_eq(v___x_68_, v___x_69_);
lean_dec(v___x_69_);
if (v_decide_70_ == 0)
{
uint32_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_71_ = lean_string_utf8_get_fast(v_str_65_, v_startInclusive_66_);
v___x_72_ = lean_box_uint32(v___x_71_);
v___x_73_ = lean_apply_1(v_inst_63_, v___x_72_);
v___x_74_ = lean_unbox(v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_string_utf8_next_fast(v_str_65_, v_startInclusive_66_);
v___x_77_ = lean_nat_sub(v___x_76_, v_startInclusive_66_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec_ref(v_inst_63_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* v_inst_80_, lean_object* v_s_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_80_, v_s_81_);
lean_dec_ref(v_s_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* v_inst_83_, lean_object* v_s_84_, lean_object* v_h_85_){
_start:
{
lean_object* v_str_86_; lean_object* v_startInclusive_87_; uint32_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_str_86_ = lean_ctor_get(v_s_84_, 0);
v_startInclusive_87_ = lean_ctor_get(v_s_84_, 1);
v___x_88_ = lean_string_utf8_get_fast(v_str_86_, v_startInclusive_87_);
v___x_89_ = lean_box_uint32(v___x_88_);
v___x_90_ = lean_apply_1(v_inst_83_, v___x_89_);
v___x_91_ = lean_unbox(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_string_utf8_next_fast(v_str_86_, v_startInclusive_87_);
v___x_94_ = lean_nat_sub(v___x_93_, v_startInclusive_87_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* v_inst_96_, lean_object* v_s_97_, lean_object* v_h_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_96_, v_s_97_, v_h_98_);
lean_dec_ref(v_s_97_);
return v_res_99_;
}
}
uint8_t l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* v_inst_100_, lean_object* v_s_101_){
_start:
{
lean_object* v_str_102_; lean_object* v_startInclusive_103_; lean_object* v_endExclusive_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v_decide_107_; 
v_str_102_ = lean_ctor_get(v_s_101_, 0);
v_startInclusive_103_ = lean_ctor_get(v_s_101_, 1);
v_endExclusive_104_ = lean_ctor_get(v_s_101_, 2);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_sub(v_endExclusive_104_, v_startInclusive_103_);
v_decide_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
if (v_decide_107_ == 0)
{
uint32_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_string_utf8_get_fast(v_str_102_, v_startInclusive_103_);
v___x_109_ = lean_box_uint32(v___x_108_);
v___x_110_ = lean_apply_1(v_inst_100_, v___x_109_);
v___x_111_ = lean_unbox(v___x_110_);
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
lean_dec_ref(v_inst_100_);
v___x_112_ = 0;
return v___x_112_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_100_ = stack[0].m_obj;
lean_object* v_s_101_ = stack[1].m_obj;
uint8_t v_res_113_;
v_res_113_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_100_, v_s_101_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* v_inst_114_, lean_object* v_s_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_114_, v_s_115_);
lean_dec_ref(v_s_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(lean_object* v_inst_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
lean_inc_ref_n(v_inst_118_, 2);
v___f_119_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v_inst_118_);
v___f_120_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_120_, 0, v_inst_118_);
v___f_121_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_121_, 0, v_inst_118_);
v___x_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_122_, 0, v___f_119_);
lean_ctor_set(v___x_122_, 1, v___f_120_);
lean_ctor_set(v___x_122_, 2, v___f_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred(lean_object* v_p_123_, lean_object* v_inst_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(v_inst_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0(lean_object* v_s_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(0u);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0___boxed(lean_object* v_s_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___lam__0(v_s_128_);
lean_dec_ref(v_s_128_);
return v_res_129_;
}
}
lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg(){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___closed__0));
return v___f_132_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_133_;
v_res_133_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg();
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___boxed(lean_object* v___dummy_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(lean_object* v_p_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___redArg___closed__0));
return v___f_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___boxed(lean_object* v_p_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(v_p_139_, v_inst_140_);
lean_dec_ref(v_inst_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(lean_object* v_p_142_, lean_object* v_s_143_){
_start:
{
lean_object* v_str_144_; lean_object* v_startInclusive_145_; lean_object* v_endExclusive_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v_decide_149_; 
v_str_144_ = lean_ctor_get(v_s_143_, 0);
v_startInclusive_145_ = lean_ctor_get(v_s_143_, 1);
v_endExclusive_146_ = lean_ctor_get(v_s_143_, 2);
v___x_147_ = lean_nat_sub(v_endExclusive_146_, v_startInclusive_145_);
v___x_148_ = lean_unsigned_to_nat(0u);
v_decide_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
if (v_decide_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint32_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_sub(v___x_147_, v___x_150_);
lean_dec(v___x_147_);
v___x_152_ = l_String_Slice_posLE(v_s_143_, v___x_151_);
v___x_153_ = lean_nat_add(v_startInclusive_145_, v___x_152_);
v___x_154_ = lean_string_utf8_get_fast(v_str_144_, v___x_153_);
lean_dec(v___x_153_);
v___x_155_ = lean_box_uint32(v___x_154_);
v___x_156_ = lean_apply_1(v_p_142_, v___x_155_);
v___x_157_ = lean_unbox(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec(v___x_152_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_152_);
return v___x_159_;
}
}
else
{
lean_object* v___x_160_; 
lean_dec(v___x_147_);
lean_dec_ref(v_p_142_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(lean_object* v_p_161_, lean_object* v_s_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(v_p_161_, v_s_162_);
lean_dec_ref(v_s_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(lean_object* v_p_164_, lean_object* v_s_165_, lean_object* v_h_166_){
_start:
{
lean_object* v_str_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint32_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_str_167_ = lean_ctor_get(v_s_165_, 0);
v_startInclusive_168_ = lean_ctor_get(v_s_165_, 1);
v_endExclusive_169_ = lean_ctor_get(v_s_165_, 2);
v___x_170_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_sub(v___x_170_, v___x_171_);
lean_dec(v___x_170_);
v___x_173_ = l_String_Slice_posLE(v_s_165_, v___x_172_);
v___x_174_ = lean_nat_add(v_startInclusive_168_, v___x_173_);
v___x_175_ = lean_string_utf8_get_fast(v_str_167_, v___x_174_);
lean_dec(v___x_174_);
v___x_176_ = lean_box_uint32(v___x_175_);
v___x_177_ = lean_apply_1(v_p_164_, v___x_176_);
v___x_178_ = lean_unbox(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
lean_dec(v___x_173_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_173_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(lean_object* v_p_181_, lean_object* v_s_182_, lean_object* v_h_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(v_p_181_, v_s_182_, v_h_183_);
lean_dec_ref(v_s_182_);
return v_res_184_;
}
}
uint8_t l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(lean_object* v_p_185_, lean_object* v_s_186_){
_start:
{
lean_object* v_str_187_; lean_object* v_startInclusive_188_; lean_object* v_endExclusive_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v_decide_192_; 
v_str_187_ = lean_ctor_get(v_s_186_, 0);
v_startInclusive_188_ = lean_ctor_get(v_s_186_, 1);
v_endExclusive_189_ = lean_ctor_get(v_s_186_, 2);
v___x_190_ = lean_nat_sub(v_endExclusive_189_, v_startInclusive_188_);
v___x_191_ = lean_unsigned_to_nat(0u);
v_decide_192_ = lean_nat_dec_eq(v___x_190_, v___x_191_);
if (v_decide_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint32_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_sub(v___x_190_, v___x_193_);
lean_dec(v___x_190_);
v___x_195_ = l_String_Slice_posLE(v_s_186_, v___x_194_);
v___x_196_ = lean_nat_add(v_startInclusive_188_, v___x_195_);
lean_dec(v___x_195_);
v___x_197_ = lean_string_utf8_get_fast(v_str_187_, v___x_196_);
lean_dec(v___x_196_);
v___x_198_ = lean_box_uint32(v___x_197_);
v___x_199_ = lean_apply_1(v_p_185_, v___x_198_);
v___x_200_ = lean_unbox(v___x_199_);
return v___x_200_;
}
else
{
uint8_t v___x_201_; 
lean_dec(v___x_190_);
lean_dec_ref(v_p_185_);
v___x_201_ = 0;
return v___x_201_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_185_ = stack[0].m_obj;
lean_object* v_s_186_ = stack[1].m_obj;
uint8_t v_res_202_;
v_res_202_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(v_p_185_, v_s_186_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(lean_object* v_p_203_, lean_object* v_s_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(v_p_203_, v_s_204_);
lean_dec_ref(v_s_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object* v_p_207_){
_start:
{
lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___x_211_; 
lean_inc_ref_n(v_p_207_, 2);
v___f_208_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed), 2, 1);
lean_closure_set(v___f_208_, 0, v_p_207_);
v___f_209_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed), 3, 1);
lean_closure_set(v___f_209_, 0, v_p_207_);
v___f_210_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed), 2, 1);
lean_closure_set(v___f_210_, 0, v_p_207_);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v___f_208_);
lean_ctor_set(v___x_211_, 1, v___f_209_);
lean_ctor_set(v___x_211_, 2, v___f_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(lean_object* v_p_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_213_, 0, lean_box(0));
lean_closure_set(v___x_213_, 1, v_p_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(lean_object* v_inst_214_, lean_object* v_s_215_){
_start:
{
lean_object* v_str_216_; lean_object* v_startInclusive_217_; lean_object* v_endExclusive_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v_decide_221_; 
v_str_216_ = lean_ctor_get(v_s_215_, 0);
v_startInclusive_217_ = lean_ctor_get(v_s_215_, 1);
v_endExclusive_218_ = lean_ctor_get(v_s_215_, 2);
v___x_219_ = lean_nat_sub(v_endExclusive_218_, v_startInclusive_217_);
v___x_220_ = lean_unsigned_to_nat(0u);
v_decide_221_ = lean_nat_dec_eq(v___x_219_, v___x_220_);
if (v_decide_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint32_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v___x_219_, v___x_222_);
lean_dec(v___x_219_);
v___x_224_ = l_String_Slice_posLE(v_s_215_, v___x_223_);
v___x_225_ = lean_nat_add(v_startInclusive_217_, v___x_224_);
v___x_226_ = lean_string_utf8_get_fast(v_str_216_, v___x_225_);
lean_dec(v___x_225_);
v___x_227_ = lean_box_uint32(v___x_226_);
v___x_228_ = lean_apply_1(v_inst_214_, v___x_227_);
v___x_229_ = lean_unbox(v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v___x_224_);
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_224_);
return v___x_231_;
}
}
else
{
lean_object* v___x_232_; 
lean_dec(v___x_219_);
lean_dec_ref(v_inst_214_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(lean_object* v_inst_233_, lean_object* v_s_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_233_, v_s_234_);
lean_dec_ref(v_s_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(lean_object* v_inst_236_, lean_object* v_s_237_, lean_object* v_h_238_){
_start:
{
lean_object* v_str_239_; lean_object* v_startInclusive_240_; lean_object* v_endExclusive_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint32_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_str_239_ = lean_ctor_get(v_s_237_, 0);
v_startInclusive_240_ = lean_ctor_get(v_s_237_, 1);
v_endExclusive_241_ = lean_ctor_get(v_s_237_, 2);
v___x_242_ = lean_nat_sub(v_endExclusive_241_, v_startInclusive_240_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_sub(v___x_242_, v___x_243_);
lean_dec(v___x_242_);
v___x_245_ = l_String_Slice_posLE(v_s_237_, v___x_244_);
v___x_246_ = lean_nat_add(v_startInclusive_240_, v___x_245_);
v___x_247_ = lean_string_utf8_get_fast(v_str_239_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_box_uint32(v___x_247_);
v___x_249_ = lean_apply_1(v_inst_236_, v___x_248_);
v___x_250_ = lean_unbox(v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec(v___x_245_);
v___x_251_ = lean_box(0);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_245_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(lean_object* v_inst_253_, lean_object* v_s_254_, lean_object* v_h_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_253_, v_s_254_, v_h_255_);
lean_dec_ref(v_s_254_);
return v_res_256_;
}
}
uint8_t l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(lean_object* v_inst_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_str_259_; lean_object* v_startInclusive_260_; lean_object* v_endExclusive_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v_decide_264_; 
v_str_259_ = lean_ctor_get(v_s_258_, 0);
v_startInclusive_260_ = lean_ctor_get(v_s_258_, 1);
v_endExclusive_261_ = lean_ctor_get(v_s_258_, 2);
v___x_262_ = lean_nat_sub(v_endExclusive_261_, v_startInclusive_260_);
v___x_263_ = lean_unsigned_to_nat(0u);
v_decide_264_ = lean_nat_dec_eq(v___x_262_, v___x_263_);
if (v_decide_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint32_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_sub(v___x_262_, v___x_265_);
lean_dec(v___x_262_);
v___x_267_ = l_String_Slice_posLE(v_s_258_, v___x_266_);
v___x_268_ = lean_nat_add(v_startInclusive_260_, v___x_267_);
lean_dec(v___x_267_);
v___x_269_ = lean_string_utf8_get_fast(v_str_259_, v___x_268_);
lean_dec(v___x_268_);
v___x_270_ = lean_box_uint32(v___x_269_);
v___x_271_ = lean_apply_1(v_inst_257_, v___x_270_);
v___x_272_ = lean_unbox(v___x_271_);
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
lean_dec(v___x_262_);
lean_dec_ref(v_inst_257_);
v___x_273_ = 0;
return v___x_273_;
}
}
}
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_257_ = stack[0].m_obj;
lean_object* v_s_258_ = stack[1].m_obj;
uint8_t v_res_274_;
v_res_274_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_257_, v_s_258_);
stack->m_num = v_res_274_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(lean_object* v_inst_275_, lean_object* v_s_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_275_, v_s_276_);
lean_dec_ref(v_s_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(lean_object* v_inst_279_){
_start:
{
lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; 
lean_inc_ref_n(v_inst_279_, 2);
v___f_280_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_280_, 0, v_inst_279_);
v___f_281_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_281_, 0, v_inst_279_);
v___f_282_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_282_, 0, v_inst_279_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v___f_280_);
lean_ctor_set(v___x_283_, 1, v___f_281_);
lean_ctor_set(v___x_283_, 2, v___f_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred(lean_object* v_p_284_, lean_object* v_inst_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(v_inst_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0(lean_object* v_s_287_){
_start:
{
lean_object* v_startInclusive_288_; lean_object* v_endExclusive_289_; lean_object* v___x_290_; 
v_startInclusive_288_ = lean_ctor_get(v_s_287_, 1);
v_endExclusive_289_ = lean_ctor_get(v_s_287_, 2);
v___x_290_ = lean_nat_sub(v_endExclusive_289_, v_startInclusive_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0___boxed(lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___lam__0(v_s_291_);
lean_dec_ref(v_s_291_);
return v_res_292_;
}
}
lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg(){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___closed__0));
return v___f_295_;
}
}
LEAN_EXPORT void l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_296_;
v_res_296_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg();
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___boxed(lean_object* v___dummy_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(lean_object* v_p_299_, lean_object* v_inst_300_){
_start:
{
lean_object* v___f_301_; 
v___f_301_ = ((lean_object*)(l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___redArg___closed__0));
return v___f_301_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___boxed(lean_object* v_p_302_, lean_object* v_inst_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(v_p_302_, v_inst_303_);
lean_dec_ref(v_inst_303_);
return v_res_304_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
