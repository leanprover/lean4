// Lean compiler output
// Module: Lean.Data.LBool
// Imports: public import Init.Data.ToString.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLBool_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedLBool;
LEAN_EXPORT uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqLBool_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqLBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqLBool_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqLBool___closed__0 = (const lean_object*)&l_Lean_instBEqLBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqLBool = (const lean_object*)&l_Lean_instBEqLBool___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LBool_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_LBool_toString___closed__0 = (const lean_object*)&l_Lean_LBool_toString___closed__0_value;
static const lean_string_object l_Lean_LBool_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_LBool_toString___closed__1 = (const lean_object*)&l_Lean_LBool_toString___closed__1_value;
static const lean_string_object l_Lean_LBool_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "undef"};
static const lean_object* l_Lean_LBool_toString___closed__2 = (const lean_object*)&l_Lean_LBool_toString___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_LBool_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LBool_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LBool_instToString___closed__0 = (const lean_object*)&l_Lean_LBool_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_LBool_instToString = (const lean_object*)&l_Lean_LBool_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Bool_toLBool(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Bool_toLBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLBoolM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LBool_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_LBool_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_LBool_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LBool_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LBool_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_LBool_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_LBool_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_LBool_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_LBool_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg(lean_object* v_false_24_){
_start:
{
lean_inc(v_false_24_);
return v_false_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg___boxed(lean_object* v_false_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_LBool_false_elim___redArg(v_false_25_);
lean_dec(v_false_25_);
return v_res_26_;
}
}
lean_object* l_Lean_LBool_false_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_false_30_){
_start:
{
lean_inc(v_false_30_);
return v_false_30_;
}
}
LEAN_EXPORT void l_Lean_LBool_false_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_false_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_LBool_false_elim(lean_box(0), v_t_28_, lean_box(0), v_false_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_false_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_LBool_false_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_false_35_);
lean_dec(v_false_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg(lean_object* v_true_38_){
_start:
{
lean_inc(v_true_38_);
return v_true_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg___boxed(lean_object* v_true_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_LBool_true_elim___redArg(v_true_39_);
lean_dec(v_true_39_);
return v_res_40_;
}
}
lean_object* l_Lean_LBool_true_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_true_44_){
_start:
{
lean_inc(v_true_44_);
return v_true_44_;
}
}
LEAN_EXPORT void l_Lean_LBool_true_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_true_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_LBool_true_elim(lean_box(0), v_t_42_, lean_box(0), v_true_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_true_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_LBool_true_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_true_49_);
lean_dec(v_true_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg(lean_object* v_undef_52_){
_start:
{
lean_inc(v_undef_52_);
return v_undef_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg___boxed(lean_object* v_undef_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_LBool_undef_elim___redArg(v_undef_53_);
lean_dec(v_undef_53_);
return v_res_54_;
}
}
lean_object* l_Lean_LBool_undef_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_undef_58_){
_start:
{
lean_inc(v_undef_58_);
return v_undef_58_;
}
}
LEAN_EXPORT void l_Lean_LBool_undef_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_undef_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_LBool_undef_elim(lean_box(0), v_t_56_, lean_box(0), v_undef_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_undef_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_LBool_undef_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_undef_63_);
lean_dec(v_undef_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
uint8_t l_Lean_instBEqLBool_beq(uint8_t v_x_68_, uint8_t v_y_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_70_ = lean_box(v_x_68_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_box(v_y_69_);
v___x_73_ = lean_obj_tag_nat(v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_nat_dec_eq(v___x_71_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_instBEqLBool_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_68_ = stack[0].m_num;
uint8_t v_y_69_ = stack[1].m_num;
uint8_t v_res_75_;
v_res_75_ = l_Lean_instBEqLBool_beq(v_x_68_, v_y_69_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqLBool_beq___boxed(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v_x_24__boxed_78_; uint8_t v_y_25__boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_x_24__boxed_78_ = lean_unbox(v_x_76_);
v_y_25__boxed_79_ = lean_unbox(v_y_77_);
v_res_80_ = l_Lean_instBEqLBool_beq(v_x_24__boxed_78_, v_y_25__boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
uint8_t l_Lean_LBool_neg(uint8_t v_x_84_){
_start:
{
switch(v_x_84_)
{
case 0:
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
case 1:
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
default: 
{
return v_x_84_;
}
}
}
}
LEAN_EXPORT void l_Lean_LBool_neg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_84_ = stack[0].m_num;
uint8_t v_res_87_;
v_res_87_ = l_Lean_LBool_neg(v_x_84_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object* v_x_88_){
_start:
{
uint8_t v_x_25__boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_x_25__boxed_89_ = lean_unbox(v_x_88_);
v_res_90_ = l_Lean_LBool_neg(v_x_25__boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
uint8_t l_Lean_LBool_and(uint8_t v_x_92_, uint8_t v_x_93_){
_start:
{
if (v_x_92_ == 1)
{
return v_x_93_;
}
else
{
return v_x_92_;
}
}
}
LEAN_EXPORT void l_Lean_LBool_and_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_92_ = stack[0].m_num;
uint8_t v_x_93_ = stack[1].m_num;
uint8_t v_res_94_;
v_res_94_ = l_Lean_LBool_and(v_x_92_, v_x_93_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_x_12__boxed_97_; uint8_t v_x_13__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_12__boxed_97_ = lean_unbox(v_x_95_);
v_x_13__boxed_98_ = lean_unbox(v_x_96_);
v_res_99_ = l_Lean_LBool_and(v_x_12__boxed_97_, v_x_13__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
lean_object* l_Lean_LBool_toString(uint8_t v_x_104_){
_start:
{
switch(v_x_104_)
{
case 0:
{
lean_object* v___x_105_; 
v___x_105_ = ((lean_object*)(l_Lean_LBool_toString___closed__0));
return v___x_105_;
}
case 1:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_Lean_LBool_toString___closed__1));
return v___x_106_;
}
default: 
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l_Lean_LBool_toString___closed__2));
return v___x_107_;
}
}
}
}
LEAN_EXPORT void l_Lean_LBool_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_104_ = stack[0].m_num;
lean_object* v_res_108_;
v_res_108_ = l_Lean_LBool_toString(v_x_104_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object* v_x_109_){
_start:
{
uint8_t v_x_31__boxed_110_; lean_object* v_res_111_; 
v_x_31__boxed_110_ = lean_unbox(v_x_109_);
v_res_111_ = l_Lean_LBool_toString(v_x_31__boxed_110_);
return v_res_111_;
}
}
uint8_t l_Lean_Bool_toLBool(uint8_t v_x_114_){
_start:
{
if (v_x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
}
LEAN_EXPORT void l_Lean_Bool_toLBool_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_114_ = stack[0].m_num;
uint8_t v_res_117_;
v_res_117_ = l_Lean_Bool_toLBool(v_x_114_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_Bool_toLBool___boxed(lean_object* v_x_118_){
_start:
{
uint8_t v_x_18__boxed_119_; uint8_t v_res_120_; lean_object* v_r_121_; 
v_x_18__boxed_119_ = lean_unbox(v_x_118_);
v_res_120_ = l_Lean_Bool_toLBool(v_x_18__boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
lean_object* l_Lean_toLBoolM___redArg___lam__0(lean_object* v_toPure_122_, uint8_t v_b_123_){
_start:
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l_Lean_Bool_toLBool(v_b_123_);
v___x_125_ = lean_box(v___x_124_);
v___x_126_ = lean_apply_2(v_toPure_122_, lean_box(0), v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_toLBoolM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_122_ = stack[0].m_obj;
uint8_t v_b_123_ = stack[1].m_num;
lean_object* v_res_127_;
v_res_127_ = l_Lean_toLBoolM___redArg___lam__0(v_toPure_122_, v_b_123_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0___boxed(lean_object* v_toPure_128_, lean_object* v_b_129_){
_start:
{
uint8_t v_b_boxed_130_; lean_object* v_res_131_; 
v_b_boxed_130_ = lean_unbox(v_b_129_);
v_res_131_ = l_Lean_toLBoolM___redArg___lam__0(v_toPure_128_, v_b_boxed_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg(lean_object* v_inst_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_toApplicative_134_; lean_object* v_toBind_135_; lean_object* v_toPure_136_; lean_object* v___f_137_; lean_object* v___x_138_; 
v_toApplicative_134_ = lean_ctor_get(v_inst_132_, 0);
lean_inc_ref(v_toApplicative_134_);
v_toBind_135_ = lean_ctor_get(v_inst_132_, 1);
lean_inc(v_toBind_135_);
lean_dec_ref(v_inst_132_);
v_toPure_136_ = lean_ctor_get(v_toApplicative_134_, 1);
lean_inc(v_toPure_136_);
lean_dec_ref(v_toApplicative_134_);
v___f_137_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_137_, 0, v_toPure_136_);
v___x_138_ = lean_apply_4(v_toBind_135_, lean_box(0), lean_box(0), v_x_133_, v___f_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM(lean_object* v_m_139_, lean_object* v_inst_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_toApplicative_142_; lean_object* v_toBind_143_; lean_object* v_toPure_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_142_ = lean_ctor_get(v_inst_140_, 0);
lean_inc_ref(v_toApplicative_142_);
v_toBind_143_ = lean_ctor_get(v_inst_140_, 1);
lean_inc(v_toBind_143_);
lean_dec_ref(v_inst_140_);
v_toPure_144_ = lean_ctor_get(v_toApplicative_142_, 1);
lean_inc(v_toPure_144_);
lean_dec_ref(v_toApplicative_142_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_145_, 0, v_toPure_144_);
v___x_146_ = lean_apply_4(v_toBind_143_, lean_box(0), lean_box(0), v_x_141_, v___f_145_);
return v___x_146_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLBool_default = _init_l_Lean_instInhabitedLBool_default();
l_Lean_instInhabitedLBool = _init_l_Lean_instInhabitedLBool();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_LBool(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_LBool(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_LBool(builtin);
}
#ifdef __cplusplus
}
#endif
