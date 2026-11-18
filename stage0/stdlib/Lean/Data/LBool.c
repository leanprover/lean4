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
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_LBool_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_LBool_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_LBool_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg(lean_object* v_false_22_){
_start:
{
lean_inc(v_false_22_);
return v_false_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___redArg___boxed(lean_object* v_false_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_LBool_false_elim___redArg(v_false_23_);
lean_dec(v_false_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_false_28_){
_start:
{
lean_inc(v_false_28_);
return v_false_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_false_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_false_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_LBool_false_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_false_32_);
lean_dec(v_false_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg(lean_object* v_true_35_){
_start:
{
lean_inc(v_true_35_);
return v_true_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___redArg___boxed(lean_object* v_true_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_LBool_true_elim___redArg(v_true_36_);
lean_dec(v_true_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_true_41_){
_start:
{
lean_inc(v_true_41_);
return v_true_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_true_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_true_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_LBool_true_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_true_45_);
lean_dec(v_true_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg(lean_object* v_undef_48_){
_start:
{
lean_inc(v_undef_48_);
return v_undef_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___redArg___boxed(lean_object* v_undef_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_LBool_undef_elim___redArg(v_undef_49_);
lean_dec(v_undef_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_undef_54_){
_start:
{
lean_inc(v_undef_54_);
return v_undef_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_undef_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_undef_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_LBool_undef_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_undef_58_);
lean_dec(v_undef_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLBool_beq(uint8_t v_x_63_, uint8_t v_y_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_65_ = lean_box(v_x_63_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_box(v_y_64_);
v___x_68_ = lean_obj_tag_nat(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = lean_nat_dec_eq(v___x_66_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLBool_beq___boxed(lean_object* v_x_70_, lean_object* v_y_71_){
_start:
{
uint8_t v_x_24__boxed_72_; uint8_t v_y_25__boxed_73_; uint8_t v_res_74_; lean_object* v_r_75_; 
v_x_24__boxed_72_ = lean_unbox(v_x_70_);
v_y_25__boxed_73_ = lean_unbox(v_y_71_);
v_res_74_ = l_Lean_instBEqLBool_beq(v_x_24__boxed_72_, v_y_25__boxed_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t v_x_78_){
_start:
{
switch(v_x_78_)
{
case 0:
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
case 1:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
default: 
{
return v_x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_x_25__boxed_82_; uint8_t v_res_83_; lean_object* v_r_84_; 
v_x_25__boxed_82_ = lean_unbox(v_x_81_);
v_res_83_ = l_Lean_LBool_neg(v_x_25__boxed_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t v_x_85_, uint8_t v_x_86_){
_start:
{
if (v_x_85_ == 1)
{
return v_x_86_;
}
else
{
return v_x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_x_12__boxed_89_; uint8_t v_x_13__boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_x_12__boxed_89_ = lean_unbox(v_x_87_);
v_x_13__boxed_90_ = lean_unbox(v_x_88_);
v_res_91_ = l_Lean_LBool_and(v_x_12__boxed_89_, v_x_13__boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t v_x_96_){
_start:
{
switch(v_x_96_)
{
case 0:
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lean_LBool_toString___closed__0));
return v___x_97_;
}
case 1:
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l_Lean_LBool_toString___closed__1));
return v___x_98_;
}
default: 
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_Lean_LBool_toString___closed__2));
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object* v_x_100_){
_start:
{
uint8_t v_x_31__boxed_101_; lean_object* v_res_102_; 
v_x_31__boxed_101_ = lean_unbox(v_x_100_);
v_res_102_ = l_Lean_LBool_toString(v_x_31__boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Bool_toLBool(uint8_t v_x_105_){
_start:
{
if (v_x_105_ == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Bool_toLBool___boxed(lean_object* v_x_108_){
_start:
{
uint8_t v_x_18__boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_x_18__boxed_109_ = lean_unbox(v_x_108_);
v_res_110_ = l_Lean_Bool_toLBool(v_x_18__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0(lean_object* v_toPure_112_, uint8_t v_b_113_){
_start:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = l_Lean_Bool_toLBool(v_b_113_);
v___x_115_ = lean_box(v___x_114_);
v___x_116_ = lean_apply_2(v_toPure_112_, lean_box(0), v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg___lam__0___boxed(lean_object* v_toPure_117_, lean_object* v_b_118_){
_start:
{
uint8_t v_b_boxed_119_; lean_object* v_res_120_; 
v_b_boxed_119_ = lean_unbox(v_b_118_);
v_res_120_ = l_Lean_toLBoolM___redArg___lam__0(v_toPure_117_, v_b_boxed_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM___redArg(lean_object* v_inst_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_toApplicative_123_; lean_object* v_toBind_124_; lean_object* v_toPure_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v_toApplicative_123_ = lean_ctor_get(v_inst_121_, 0);
lean_inc_ref(v_toApplicative_123_);
v_toBind_124_ = lean_ctor_get(v_inst_121_, 1);
lean_inc(v_toBind_124_);
lean_dec_ref(v_inst_121_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_123_, 1);
lean_inc(v_toPure_125_);
lean_dec_ref(v_toApplicative_123_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_126_, 0, v_toPure_125_);
v___x_127_ = lean_apply_4(v_toBind_124_, lean_box(0), lean_box(0), v_x_122_, v___f_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLBoolM(lean_object* v_m_128_, lean_object* v_inst_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_toApplicative_131_; lean_object* v_toBind_132_; lean_object* v_toPure_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v_toApplicative_131_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_131_);
v_toBind_132_ = lean_ctor_get(v_inst_129_, 1);
lean_inc(v_toBind_132_);
lean_dec_ref(v_inst_129_);
v_toPure_133_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_inc(v_toPure_133_);
lean_dec_ref(v_toApplicative_131_);
v___f_134_ = lean_alloc_closure((void*)(l_Lean_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_134_, 0, v_toPure_133_);
v___x_135_ = lean_apply_4(v_toBind_132_, lean_box(0), lean_box(0), v_x_130_, v___f_134_);
return v___x_135_;
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
