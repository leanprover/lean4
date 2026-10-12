// Lean compiler output
// Module: Init.Data.Array.Lex.Lemmas
// Imports: import all Init.Data.Array.Lex.Basic public import Init.Data.Array.Lex.Basic import Init.Data.Range.Polymorphic.NatLemmas public import Init.Data.BEq import Init.Data.Array.DecidableEq import Init.Data.Array.Lemmas import Init.Data.Bool import Init.Data.List.Lex import Init.Data.Range.Polymorphic.Lemmas
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_lex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_lex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLt___redArg();
LEAN_EXPORT lean_object* l_Array_instTransLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLTOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v_a_20_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v_x_17_, 1);
v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_a_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_x_17_, 1);
v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_24_, lean_object* v_motive_25_, lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v_a_29_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v_x_26_, 1);
v___x_30_ = lean_apply_1(v_h__1_27_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_a_31_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_x_26_, 1);
v___x_32_ = lean_apply_1(v_h__2_28_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_lex_match__1_splitter___redArg(lean_object* v_l_u2081_33_, lean_object* v_l_u2082_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_){
_start:
{
if (lean_obj_tag(v_l_u2081_33_) == 0)
{
lean_dec(v_h__3_37_);
if (lean_obj_tag(v_l_u2082_34_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_h__1_35_);
v___x_38_ = lean_apply_1(v_h__2_36_, v_l_u2082_34_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_36_);
v_head_39_ = lean_ctor_get(v_l_u2082_34_, 0);
lean_inc(v_head_39_);
v_tail_40_ = lean_ctor_get(v_l_u2082_34_, 1);
lean_inc(v_tail_40_);
lean_dec_ref_known(v_l_u2082_34_, 2);
v___x_41_ = lean_apply_2(v_h__1_35_, v_head_39_, v_tail_40_);
return v___x_41_;
}
}
else
{
lean_dec(v_h__1_35_);
if (lean_obj_tag(v_l_u2082_34_) == 0)
{
lean_object* v___x_42_; 
lean_dec(v_h__3_37_);
v___x_42_ = lean_apply_1(v_h__2_36_, v_l_u2081_33_);
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_36_);
v_head_43_ = lean_ctor_get(v_l_u2081_33_, 0);
lean_inc(v_head_43_);
v_tail_44_ = lean_ctor_get(v_l_u2081_33_, 1);
lean_inc(v_tail_44_);
lean_dec_ref_known(v_l_u2081_33_, 2);
v_head_45_ = lean_ctor_get(v_l_u2082_34_, 0);
lean_inc(v_head_45_);
v_tail_46_ = lean_ctor_get(v_l_u2082_34_, 1);
lean_inc(v_tail_46_);
lean_dec_ref_known(v_l_u2082_34_, 2);
v___x_47_ = lean_apply_4(v_h__3_37_, v_head_43_, v_tail_44_, v_head_45_, v_tail_46_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Lex_Lemmas_0__List_lex_match__1_splitter(lean_object* v_00_u03b1_48_, lean_object* v_motive_49_, lean_object* v_l_u2081_50_, lean_object* v_l_u2082_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_, lean_object* v_h__3_54_){
_start:
{
if (lean_obj_tag(v_l_u2081_50_) == 0)
{
lean_dec(v_h__3_54_);
if (lean_obj_tag(v_l_u2082_51_) == 0)
{
lean_object* v___x_55_; 
lean_dec(v_h__1_52_);
v___x_55_ = lean_apply_1(v_h__2_53_, v_l_u2082_51_);
return v___x_55_;
}
else
{
lean_object* v_head_56_; lean_object* v_tail_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_53_);
v_head_56_ = lean_ctor_get(v_l_u2082_51_, 0);
lean_inc(v_head_56_);
v_tail_57_ = lean_ctor_get(v_l_u2082_51_, 1);
lean_inc(v_tail_57_);
lean_dec_ref_known(v_l_u2082_51_, 2);
v___x_58_ = lean_apply_2(v_h__1_52_, v_head_56_, v_tail_57_);
return v___x_58_;
}
}
else
{
lean_dec(v_h__1_52_);
if (lean_obj_tag(v_l_u2082_51_) == 0)
{
lean_object* v___x_59_; 
lean_dec(v_h__3_54_);
v___x_59_ = lean_apply_1(v_h__2_53_, v_l_u2081_50_);
return v___x_59_;
}
else
{
lean_object* v_head_60_; lean_object* v_tail_61_; lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_53_);
v_head_60_ = lean_ctor_get(v_l_u2081_50_, 0);
lean_inc(v_head_60_);
v_tail_61_ = lean_ctor_get(v_l_u2081_50_, 1);
lean_inc(v_tail_61_);
lean_dec_ref_known(v_l_u2081_50_, 2);
v_head_62_ = lean_ctor_get(v_l_u2082_51_, 0);
lean_inc(v_head_62_);
v_tail_63_ = lean_ctor_get(v_l_u2082_51_, 1);
lean_inc(v_tail_63_);
lean_dec_ref_known(v_l_u2082_51_, 2);
v___x_64_ = lean_apply_4(v_h__3_54_, v_head_60_, v_tail_61_, v_head_62_, v_tail_63_);
return v___x_64_;
}
}
}
}
lean_object* l_Array_instTransLt___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT void l_Array_instTransLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_67_;
v_res_67_ = l_Array_instTransLt___redArg();
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Array_instTransLt___redArg___boxed(lean_object* v___dummy_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Array_instTransLt___redArg();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransLt(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg(){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
LEAN_EXPORT void l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_76_;
v_res_76_ = l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Array_instTransLeOfLawfulOrderLTOfIsLinearOrder(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
uint8_t l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(lean_object* v_inst_85_, lean_object* v_x1_86_, lean_object* v_x2_87_){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_apply_2(v_inst_85_, v_x1_86_, v_x2_87_);
v___x_89_ = lean_unbox(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT void l_Array_instDecidableLTOfDecidableEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_85_ = stack[0].m_obj;
lean_object* v_x1_86_ = stack[1].m_obj;
lean_object* v_x2_87_ = stack[2].m_obj;
uint8_t v_res_90_;
v_res_90_ = l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_85_, v_x1_86_, v_x2_87_);
stack->m_num = v_res_90_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed(lean_object* v_inst_91_, lean_object* v_x1_92_, lean_object* v_x2_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Array_instDecidableLTOfDecidableEq___redArg___lam__0(v_inst_91_, v_x1_92_, v_x2_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
uint8_t l_Array_instDecidableLTOfDecidableEq___redArg(lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_xs_98_, lean_object* v_ys_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___f_101_; uint8_t v___x_102_; 
v___f_100_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_100_, 0, v_inst_97_);
v___f_101_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_101_, 0, v_inst_96_);
v___x_102_ = l_Array_lex___redArg(v___f_101_, v_xs_98_, v_ys_99_, v___f_100_);
return v___x_102_;
}
}
LEAN_EXPORT void l_Array_instDecidableLTOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_96_ = stack[0].m_obj;
lean_object* v_inst_97_ = stack[1].m_obj;
lean_object* v_xs_98_ = stack[2].m_obj;
lean_object* v_ys_99_ = stack[3].m_obj;
uint8_t v_res_103_;
v_res_103_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_96_, v_inst_97_, v_xs_98_, v_ys_99_);
stack->m_num = v_res_103_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___redArg___boxed(lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_xs_106_, lean_object* v_ys_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_104_, v_inst_105_, v_xs_106_, v_ys_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
uint8_t l_Array_instDecidableLTOfDecidableEq(lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_xs_114_, lean_object* v_ys_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Array_instDecidableLTOfDecidableEq___redArg(v_inst_111_, v_inst_113_, v_xs_114_, v_ys_115_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Array_instDecidableLTOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_111_ = stack[1].m_obj;
lean_object* v_inst_112_ = stack[2].m_obj;
lean_object* v_inst_113_ = stack[3].m_obj;
lean_object* v_xs_114_ = stack[4].m_obj;
lean_object* v_ys_115_ = stack[5].m_obj;
uint8_t v_res_117_;
v_res_117_ = l_Array_instDecidableLTOfDecidableEq(lean_box(0), v_inst_111_, v_inst_112_, v_inst_113_, v_xs_114_, v_ys_115_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableLTOfDecidableEq___boxed(lean_object* v_00_u03b1_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_xs_122_, lean_object* v_ys_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Array_instDecidableLTOfDecidableEq(v_00_u03b1_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_xs_122_, v_ys_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_xs_128_, lean_object* v_ys_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___f_131_; uint8_t v___x_132_; 
v___f_130_ = lean_alloc_closure((void*)(l_Array_instDecidableLTOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_130_, 0, v_inst_127_);
v___f_131_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_131_, 0, v_inst_126_);
v___x_132_ = l_Array_lex___redArg(v___f_131_, v_ys_129_, v_xs_128_, v___f_130_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
}
LEAN_EXPORT void l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_126_ = stack[0].m_obj;
lean_object* v_inst_127_ = stack[1].m_obj;
lean_object* v_xs_128_ = stack[2].m_obj;
lean_object* v_ys_129_ = stack[3].m_obj;
uint8_t v_res_135_;
v_res_135_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_126_, v_inst_127_, v_xs_128_, v_ys_129_);
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg___boxed(lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_xs_138_, lean_object* v_ys_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_136_, v_inst_137_, v_xs_138_, v_ys_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
uint8_t l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_object* v_00_u03b1_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_xs_146_, lean_object* v_ys_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT___redArg(v_inst_143_, v_inst_145_, v_xs_146_, v_ys_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Array_instDecidableLEOfDecidableEqOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_143_ = stack[1].m_obj;
lean_object* v_inst_144_ = stack[2].m_obj;
lean_object* v_inst_145_ = stack[3].m_obj;
lean_object* v_xs_146_ = stack[4].m_obj;
lean_object* v_ys_147_ = stack[5].m_obj;
uint8_t v_res_149_;
v_res_149_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(lean_box(0), v_inst_143_, v_inst_144_, v_inst_145_, v_xs_146_, v_ys_147_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_Array_instDecidableLEOfDecidableEqOfDecidableLT___boxed(lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_xs_154_, lean_object* v_ys_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Array_instDecidableLEOfDecidableEqOfDecidableLT(v_00_u03b1_150_, v_inst_151_, v_inst_152_, v_inst_153_, v_xs_154_, v_ys_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Lex_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Lex_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Lex_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
