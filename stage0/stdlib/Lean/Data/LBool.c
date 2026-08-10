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
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_LBool_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg(lean_object* v_false_23_){
_start:
{
lean_inc(v_false_23_);
return v_false_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg___boxed(lean_object* v_false_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LBool_false_elim___redArg(v_false_24_);
lean_dec(v_false_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_false_29_){
_start:
{
lean_inc(v_false_29_);
return v_false_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_false_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_LBool_false_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_false_33_);
lean_dec(v_false_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg(lean_object* v_true_36_){
_start:
{
lean_inc(v_true_36_);
return v_true_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg___boxed(lean_object* v_true_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_LBool_true_elim___redArg(v_true_37_);
lean_dec(v_true_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_true_42_){
_start:
{
lean_inc(v_true_42_);
return v_true_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_true_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_LBool_true_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_true_46_);
lean_dec(v_true_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg(lean_object* v_undef_49_){
_start:
{
lean_inc(v_undef_49_);
return v_undef_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg___boxed(lean_object* v_undef_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_LBool_undef_elim___redArg(v_undef_50_);
lean_dec(v_undef_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_undef_55_){
_start:
{
lean_inc(v_undef_55_);
return v_undef_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_undef_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_LBool_undef_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_undef_59_);
lean_dec(v_undef_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLBool_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_LBool_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_LBool_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLBool_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_17__boxed_71_; uint8_t v_y_18__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_17__boxed_71_ = lean_unbox(v_x_69_);
v_y_18__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqLBool_beq(v_x_17__boxed_71_, v_y_18__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t v_x_77_){
_start:
{
switch(v_x_77_)
{
case 0:
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
case 1:
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
default: 
{
return v_x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object* v_x_80_){
_start:
{
uint8_t v_x_25__boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_x_25__boxed_81_ = lean_unbox(v_x_80_);
v_res_82_ = l_Lean_LBool_neg(v_x_25__boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t v_x_84_, uint8_t v_x_85_){
_start:
{
if (v_x_84_ == 1)
{
return v_x_85_;
}
else
{
return v_x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
uint8_t v_x_16__boxed_88_; uint8_t v_x_17__boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_x_16__boxed_88_ = lean_unbox(v_x_86_);
v_x_17__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Lean_LBool_and(v_x_16__boxed_88_, v_x_17__boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t v_x_95_){
_start:
{
switch(v_x_95_)
{
case 0:
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Lean_LBool_toString___closed__0));
return v___x_96_;
}
case 1:
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lean_LBool_toString___closed__1));
return v___x_97_;
}
default: 
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Lean_LBool_toString___closed__2));
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object* v_x_99_){
_start:
{
uint8_t v_x_31__boxed_100_; lean_object* v_res_101_; 
v_x_31__boxed_100_ = lean_unbox(v_x_99_);
v_res_101_ = l_Lean_LBool_toString(v_x_31__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Bool_toLBool(uint8_t v_x_104_){
_start:
{
if (v_x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Bool_toLBool___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_x_18__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_x_18__boxed_108_ = lean_unbox(v_x_107_);
v_res_109_ = l_Lean_Bool_toLBool(v_x_18__boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0(lean_object* v_toPure_111_, uint8_t v_b_112_){
_start:
{
uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_Bool_toLBool(v_b_112_);
v___x_114_ = lean_box(v___x_113_);
v___x_115_ = lean_apply_2(v_toPure_111_, lean_box(0), v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0___boxed(lean_object* v_toPure_116_, lean_object* v_b_117_){
_start:
{
uint8_t v_b_boxed_118_; lean_object* v_res_119_; 
v_b_boxed_118_ = lean_unbox(v_b_117_);
v_res_119_ = l_Lean_toLBoolM___redArg___lam__0(v_toPure_116_, v_b_boxed_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg(lean_object* v_inst_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_toApplicative_122_; lean_object* v_toBind_123_; lean_object* v_toPure_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
v_toApplicative_122_ = lean_ctor_get(v_inst_120_, 0);
lean_inc_ref(v_toApplicative_122_);
v_toBind_123_ = lean_ctor_get(v_inst_120_, 1);
lean_inc(v_toBind_123_);
lean_dec_ref(v_inst_120_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_122_, 1);
lean_inc(v_toPure_124_);
lean_dec_ref(v_toApplicative_122_);
v___f_125_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_125_, 0, v_toPure_124_);
v___x_126_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v_x_121_, v___f_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM(lean_object* v_m_127_, lean_object* v_inst_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toBind_131_; lean_object* v_toPure_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_128_, 0);
lean_inc_ref(v_toApplicative_130_);
v_toBind_131_ = lean_ctor_get(v_inst_128_, 1);
lean_inc(v_toBind_131_);
lean_dec_ref(v_inst_128_);
v_toPure_132_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_inc(v_toPure_132_);
lean_dec_ref(v_toApplicative_130_);
v___f_133_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_133_, 0, v_toPure_132_);
v___x_134_ = lean_apply_4(v_toBind_131_, lean_box(0), lean_box(0), v_x_129_, v___f_133_);
return v___x_134_;
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
