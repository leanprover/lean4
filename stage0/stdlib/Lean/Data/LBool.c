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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Bool_toLBool(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toLBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLBoolM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLBoolM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LBool_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_LBool_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_LBool_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_LBool_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_LBool_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg(lean_object* v_false_28_){
_start:
{
lean_inc(v_false_28_);
return v_false_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg___boxed(lean_object* v_false_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_LBool_false_elim___redArg(v_false_29_);
lean_dec(v_false_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_false_34_){
_start:
{
lean_inc(v_false_34_);
return v_false_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_false_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_LBool_false_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_false_38_);
lean_dec(v_false_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg(lean_object* v_true_41_){
_start:
{
lean_inc(v_true_41_);
return v_true_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg___boxed(lean_object* v_true_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_LBool_true_elim___redArg(v_true_42_);
lean_dec(v_true_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_true_47_){
_start:
{
lean_inc(v_true_47_);
return v_true_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_true_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_LBool_true_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_true_51_);
lean_dec(v_true_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg(lean_object* v_undef_54_){
_start:
{
lean_inc(v_undef_54_);
return v_undef_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg___boxed(lean_object* v_undef_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_LBool_undef_elim___redArg(v_undef_55_);
lean_dec(v_undef_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_undef_60_){
_start:
{
lean_inc(v_undef_60_);
return v_undef_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_undef_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_LBool_undef_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_undef_64_);
lean_dec(v_undef_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLBool_beq(uint8_t v_x_69_, uint8_t v_y_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_Lean_LBool_ctorIdx(v_x_69_);
v___x_72_ = l_Lean_LBool_ctorIdx(v_y_70_);
v___x_73_ = lean_nat_dec_eq(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLBool_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_17__boxed_76_; uint8_t v_y_18__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_17__boxed_76_ = lean_unbox(v_x_74_);
v_y_18__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_instBEqLBool_beq(v_x_17__boxed_76_, v_y_18__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t v_x_82_){
_start:
{
switch(v_x_82_)
{
case 0:
{
uint8_t v___x_83_; 
v___x_83_ = 1;
return v___x_83_;
}
case 1:
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
default: 
{
return v_x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object* v_x_85_){
_start:
{
uint8_t v_x_25__boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_x_25__boxed_86_ = lean_unbox(v_x_85_);
v_res_87_ = l_Lean_LBool_neg(v_x_25__boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t v_x_89_, uint8_t v_x_90_){
_start:
{
if (v_x_89_ == 1)
{
return v_x_90_;
}
else
{
return v_x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v_x_16__boxed_93_; uint8_t v_x_17__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_x_16__boxed_93_ = lean_unbox(v_x_91_);
v_x_17__boxed_94_ = lean_unbox(v_x_92_);
v_res_95_ = l_Lean_LBool_and(v_x_16__boxed_93_, v_x_17__boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t v_x_100_){
_start:
{
switch(v_x_100_)
{
case 0:
{
lean_object* v___x_101_; 
v___x_101_ = ((lean_object*)(l_Lean_LBool_toString___closed__0));
return v___x_101_;
}
case 1:
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l_Lean_LBool_toString___closed__1));
return v___x_102_;
}
default: 
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l_Lean_LBool_toString___closed__2));
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object* v_x_104_){
_start:
{
uint8_t v_x_31__boxed_105_; lean_object* v_res_106_; 
v_x_31__boxed_105_ = lean_unbox(v_x_104_);
v_res_106_ = l_Lean_LBool_toString(v_x_31__boxed_105_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l_Bool_toLBool(uint8_t v_x_109_){
_start:
{
if (v_x_109_ == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toLBool___boxed(lean_object* v_x_112_){
_start:
{
uint8_t v_x_18__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_18__boxed_113_ = lean_unbox(v_x_112_);
v_res_114_ = l_Bool_toLBool(v_x_18__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0(lean_object* v_toPure_116_, uint8_t v_b_117_){
_start:
{
uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = l_Bool_toLBool(v_b_117_);
v___x_119_ = lean_box(v___x_118_);
v___x_120_ = lean_apply_2(v_toPure_116_, lean_box(0), v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0___boxed(lean_object* v_toPure_121_, lean_object* v_b_122_){
_start:
{
uint8_t v_b_boxed_123_; lean_object* v_res_124_; 
v_b_boxed_123_ = lean_unbox(v_b_122_);
v_res_124_ = l_toLBoolM___redArg___lam__0(v_toPure_121_, v_b_boxed_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg(lean_object* v_inst_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_toApplicative_127_; lean_object* v_toBind_128_; lean_object* v_toPure_129_; lean_object* v___f_130_; lean_object* v___x_131_; 
v_toApplicative_127_ = lean_ctor_get(v_inst_125_, 0);
lean_inc_ref(v_toApplicative_127_);
v_toBind_128_ = lean_ctor_get(v_inst_125_, 1);
lean_inc(v_toBind_128_);
lean_dec_ref(v_inst_125_);
v_toPure_129_ = lean_ctor_get(v_toApplicative_127_, 1);
lean_inc(v_toPure_129_);
lean_dec_ref(v_toApplicative_127_);
v___f_130_ = lean_alloc_closure((void*)(l_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_130_, 0, v_toPure_129_);
v___x_131_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v_x_126_, v___f_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_toLBoolM(lean_object* v_m_132_, lean_object* v_inst_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toBind_136_; lean_object* v_toPure_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toApplicative_135_);
v_toBind_136_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toBind_136_);
lean_dec_ref(v_inst_133_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_135_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_135_);
v___f_138_ = lean_alloc_closure((void*)(l_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_138_, 0, v_toPure_137_);
v___x_139_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v_x_134_, v___f_138_);
return v___x_139_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
