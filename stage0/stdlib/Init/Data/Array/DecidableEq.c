// Lean compiler output
// Module: Init.Data.Array.DecidableEq
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Basic public import Init.Data.Nat.Lemmas import Init.ByCases import Init.Classical import Init.Data.BEq import Init.Data.Bool import Init.Data.List.Nat.BEq import Init.RCases
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_a_2_, v_b_3_);
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___lam__0___boxed(lean_object* v_inst_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_6_, v_a_7_, v_b_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___redArg(lean_object* v_inst_11_, lean_object* v_xs_12_, lean_object* v_ys_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_14_ = lean_array_get_size(v_xs_12_);
v___x_15_ = lean_array_get_size(v_ys_13_);
v___x_16_ = lean_nat_dec_eq(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_dec_ref(v_inst_11_);
return v___x_16_;
}
else
{
lean_object* v___f_17_; uint8_t v___x_18_; 
v___f_17_ = lean_alloc_closure((void*)(l_Array_instDecidableEqImpl___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_17_, 0, v_inst_11_);
v___x_18_ = l_Array_isEqvAux___redArg(v_xs_12_, v_ys_13_, v___f_17_, v___x_14_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___redArg___boxed(lean_object* v_inst_19_, lean_object* v_xs_20_, lean_object* v_ys_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Array_instDecidableEqImpl___redArg(v_inst_19_, v_xs_20_, v_ys_21_);
lean_dec_ref(v_ys_21_);
lean_dec_ref(v_xs_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_xs_26_, lean_object* v_ys_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_Array_instDecidableEqImpl___redArg(v_inst_25_, v_xs_26_, v_ys_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_xs_31_, lean_object* v_ys_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Array_instDecidableEqImpl(v_00_u03b1_29_, v_inst_30_, v_xs_31_, v_ys_32_);
lean_dec_ref(v_ys_32_);
lean_dec_ref(v_xs_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq___redArg(lean_object* v_inst_35_, lean_object* v_xs_36_, lean_object* v_ys_37_){
_start:
{
lean_object* v_toList_38_; 
lean_inc_ref(v_xs_36_);
v_toList_38_ = lean_array_to_list(v_xs_36_);
if (lean_obj_tag(v_toList_38_) == 0)
{
lean_object* v_toList_39_; 
lean_dec_ref(v_xs_36_);
lean_dec_ref(v_inst_35_);
v_toList_39_ = lean_array_to_list(v_ys_37_);
if (lean_obj_tag(v_toList_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
lean_dec_ref_known(v_toList_39_, 2);
v___x_41_ = 0;
return v___x_41_;
}
}
else
{
lean_object* v_toList_42_; 
lean_dec_ref_known(v_toList_38_, 2);
lean_inc_ref(v_ys_37_);
v_toList_42_ = lean_array_to_list(v_ys_37_);
if (lean_obj_tag(v_toList_42_) == 0)
{
uint8_t v___x_43_; 
lean_dec_ref(v_ys_37_);
lean_dec_ref(v_xs_36_);
lean_dec_ref(v_inst_35_);
v___x_43_ = 0;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
lean_dec_ref_known(v_toList_42_, 2);
v___x_44_ = l_Array_instDecidableEqImpl___redArg(v_inst_35_, v_xs_36_, v_ys_37_);
lean_dec_ref(v_ys_37_);
lean_dec_ref(v_xs_36_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___redArg___boxed(lean_object* v_inst_45_, lean_object* v_xs_46_, lean_object* v_ys_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Array_instDecidableEq___redArg(v_inst_45_, v_xs_46_, v_ys_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEq(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_xs_52_, lean_object* v_ys_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = l_Array_instDecidableEq___redArg(v_inst_51_, v_xs_52_, v_ys_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEq___boxed(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_xs_57_, lean_object* v_ys_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Array_instDecidableEq(v_00_u03b1_55_, v_inst_56_, v_xs_57_, v_ys_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp___redArg(lean_object* v_xs_61_){
_start:
{
lean_object* v_toList_62_; 
v_toList_62_ = lean_array_to_list(v_xs_61_);
if (lean_obj_tag(v_toList_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 1;
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
lean_dec_ref_known(v_toList_62_, 2);
v___x_64_ = 0;
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___redArg___boxed(lean_object* v_xs_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Array_instDecidableEqEmp___redArg(v_xs_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmp(lean_object* v_00_u03b1_68_, lean_object* v_xs_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_Array_instDecidableEqEmp___redArg(v_xs_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmp___boxed(lean_object* v_00_u03b1_71_, lean_object* v_xs_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Array_instDecidableEqEmp(v_00_u03b1_71_, v_xs_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq___redArg(lean_object* v_ys_75_){
_start:
{
lean_object* v_toList_76_; 
v_toList_76_ = lean_array_to_list(v_ys_75_);
if (lean_obj_tag(v_toList_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
lean_dec_ref_known(v_toList_76_, 2);
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___redArg___boxed(lean_object* v_ys_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Array_instDecidableEmpEq___redArg(v_ys_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEq(lean_object* v_00_u03b1_82_, lean_object* v_ys_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_Array_instDecidableEmpEq___redArg(v_ys_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEq___boxed(lean_object* v_00_u03b1_85_, lean_object* v_ys_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Array_instDecidableEmpEq(v_00_u03b1_85_, v_ys_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl___redArg(lean_object* v_xs_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = lean_array_get_size(v_xs_89_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_nat_dec_eq(v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___redArg___boxed(lean_object* v_xs_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_93_);
lean_dec_ref(v_xs_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqEmpImpl(lean_object* v_00_u03b1_96_, lean_object* v_xs_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_array_get_size(v_xs_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqEmpImpl___boxed(lean_object* v_00_u03b1_101_, lean_object* v_xs_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_101_, v_xs_102_);
lean_dec_ref(v_xs_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl___redArg(lean_object* v_xs_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_array_get_size(v_xs_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___redArg___boxed(lean_object* v_xs_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_109_);
lean_dec_ref(v_xs_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEmpEqImpl(lean_object* v_00_u03b1_112_, lean_object* v_xs_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_array_get_size(v_xs_113_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_dec_eq(v___x_114_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEmpEqImpl___boxed(lean_object* v_00_u03b1_117_, lean_object* v_xs_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_117_, v_xs_118_);
lean_dec_ref(v_xs_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_BEq(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_DecidableEq(builtin);
}
#ifdef __cplusplus
}
#endif
