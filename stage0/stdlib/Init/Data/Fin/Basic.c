// Lean compiler output
// Module: Init.Data.Fin.Basic
// Imports: public import Init.Data.Nat.Bitwise.Basic public import Init.Data.Nat.Basic import Init.Data.Nat.Div.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Fin_coeToNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_coeToNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_coeToNat___closed__0 = (const lean_object*)&l_Fin_coeToNat___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_land(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_xor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instXorOp(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_last(lean_object*);
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0(lean_object* v_v_1_){
_start:
{
lean_inc(v_v_1_);
return v_v_1_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0___boxed(lean_object* v_v_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Fin_coeToNat___lam__0(v_v_2_);
lean_dec(v_v_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object* v_n_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l_Fin_coeToNat___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Fin_coeToNat(v_n_7_);
lean_dec(v_n_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object* v_00_u03b1_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Fin_elim0(v_00_u03b1_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_x_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Fin_succ___redArg(v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ(lean_object* v_n_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Fin_succ___redArg(v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object* v_n_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Fin_succ(v_n_22_, v_x_23_);
lean_dec(v_x_23_);
lean_dec(v_n_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object* v_n_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_nat_mod(v_a_26_, v_n_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object* v_n_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Fin_ofNat___redArg(v_n_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec(v_n_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object* v_n_31_, lean_object* v_inst_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_nat_mod(v_a_33_, v_n_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Fin_ofNat(v_n_35_, v_inst_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec(v_n_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object* v_i_39_){
_start:
{
lean_inc(v_i_39_);
return v_i_39_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object* v_i_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Fin_toNat___redArg(v_i_40_);
lean_dec(v_i_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object* v_n_42_, lean_object* v_i_43_){
_start:
{
lean_inc(v_i_43_);
return v_i_43_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object* v_n_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Fin_toNat(v_n_44_, v_i_45_);
lean_dec(v_i_45_);
lean_dec(v_n_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Fin_add(lean_object* v_n_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_nat_add(v_x_48_, v_x_49_);
v___x_51_ = lean_nat_mod(v___x_50_, v_n_47_);
lean_dec(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object* v_n_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Fin_add(v_n_52_, v_x_53_, v_x_54_);
lean_dec(v_x_54_);
lean_dec(v_x_53_);
lean_dec(v_n_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul(lean_object* v_n_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_nat_mul(v_x_57_, v_x_58_);
v___x_60_ = lean_nat_mod(v___x_59_, v_n_56_);
lean_dec(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object* v_n_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Fin_mul(v_n_61_, v_x_62_, v_x_63_);
lean_dec(v_x_63_);
lean_dec(v_x_62_);
lean_dec(v_n_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub(lean_object* v_n_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_nat_sub(v_n_65_, v_x_67_);
v___x_69_ = lean_nat_add(v___x_68_, v_x_66_);
lean_dec(v___x_68_);
v___x_70_ = lean_nat_mod(v___x_69_, v_n_65_);
lean_dec(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object* v_n_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Fin_sub(v_n_71_, v_x_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec(v_x_72_);
lean_dec(v_n_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_nat_mod(v_x_75_, v_x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Fin_mod___redArg(v_x_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_x_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod(lean_object* v_n_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_nat_mod(v_x_82_, v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object* v_n_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Fin_mod(v_n_85_, v_x_86_, v_x_87_);
lean_dec(v_x_87_);
lean_dec(v_x_86_);
lean_dec(v_n_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_nat_div(v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Fin_div___redArg(v_x_92_, v_x_93_);
lean_dec(v_x_93_);
lean_dec(v_x_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Fin_div(lean_object* v_n_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_nat_div(v_x_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object* v_n_99_, lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Fin_div(v_n_99_, v_x_100_, v_x_101_);
lean_dec(v_x_101_);
lean_dec(v_x_100_);
lean_dec(v_n_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_nat_mod(v_x_103_, v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Fin_modn___redArg(v_x_106_, v_x_107_);
lean_dec(v_x_107_);
lean_dec(v_x_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn(lean_object* v_n_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_nat_mod(v_x_110_, v_x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object* v_n_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Fin_modn(v_n_113_, v_x_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec(v_x_114_);
lean_dec(v_n_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Fin_land(lean_object* v_n_117_, lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_nat_land(v_x_118_, v_x_119_);
v___x_121_ = lean_nat_mod(v___x_120_, v_n_117_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object* v_n_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Fin_land(v_n_122_, v_x_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_x_123_);
lean_dec(v_n_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor(lean_object* v_n_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_nat_lor(v_x_127_, v_x_128_);
v___x_130_ = lean_nat_mod(v___x_129_, v_n_126_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object* v_n_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Fin_lor(v_n_131_, v_x_132_, v_x_133_);
lean_dec(v_x_133_);
lean_dec(v_x_132_);
lean_dec(v_n_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor(lean_object* v_n_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_lxor(v_x_136_, v_x_137_);
v___x_139_ = lean_nat_mod(v___x_138_, v_n_135_);
lean_dec(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object* v_n_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Fin_xor(v_n_140_, v_x_141_, v_x_142_);
lean_dec(v_x_142_);
lean_dec(v_x_141_);
lean_dec(v_n_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object* v_n_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_nat_shiftl(v_x_145_, v_x_146_);
v___x_148_ = lean_nat_mod(v___x_147_, v_n_144_);
lean_dec(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object* v_n_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Fin_shiftLeft(v_n_149_, v_x_150_, v_x_151_);
lean_dec(v_x_151_);
lean_dec(v_x_150_);
lean_dec(v_n_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object* v_n_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_nat_shiftr(v_x_154_, v_x_155_);
v___x_157_ = lean_nat_mod(v___x_156_, v_n_153_);
lean_dec(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object* v_n_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Fin_shiftRight(v_n_158_, v_x_159_, v_x_160_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
lean_dec(v_n_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object* v_n_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(v___x_163_, 0, v_n_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object* v_n_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(v___x_165_, 0, v_n_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object* v_n_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_167_, 0, v_n_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object* v_n_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_closure((void*)(l_Fin_mod___boxed), 3, 1);
lean_closure_set(v___x_169_, 0, v_n_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object* v_n_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_closure((void*)(l_Fin_div___boxed), 3, 1);
lean_closure_set(v___x_171_, 0, v_n_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object* v_n_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_closure((void*)(l_Fin_land___boxed), 3, 1);
lean_closure_set(v___x_173_, 0, v_n_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object* v_n_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_closure((void*)(l_Fin_lor___boxed), 3, 1);
lean_closure_set(v___x_175_, 0, v_n_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Fin_instXorOp(lean_object* v_n_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_closure((void*)(l_Fin_xor___boxed), 3, 1);
lean_closure_set(v___x_177_, 0, v_n_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object* v_n_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_closure((void*)(l_Fin_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_179_, 0, v_n_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object* v_n_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_closure((void*)(l_Fin_shiftRight___boxed), 3, 1);
lean_closure_set(v___x_181_, 0, v_n_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object* v_n_182_, lean_object* v_i_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_nat_mod(v_i_183_, v_n_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object* v_n_185_, lean_object* v_i_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Fin_instOfNat___redArg(v_n_185_, v_i_186_);
lean_dec(v_i_186_);
lean_dec(v_n_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object* v_n_188_, lean_object* v_inst_189_, lean_object* v_i_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_nat_mod(v_i_190_, v_n_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object* v_n_192_, lean_object* v_inst_193_, lean_object* v_i_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Fin_instOfNat(v_n_192_, v_inst_193_, v_i_194_);
lean_dec(v_i_194_);
lean_dec(v_n_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object* v_n_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_nat_sub(v_n_196_, v_a_197_);
v___x_199_ = lean_nat_mod(v___x_198_, v_n_196_);
lean_dec(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object* v_n_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Fin_neg___lam__0(v_n_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec(v_n_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg(lean_object* v_n_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_204_, 0, v_n_203_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg(lean_object* v_n_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_mod(v___x_206_, v_n_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object* v_n_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Fin_instInhabited___redArg(v_n_208_);
lean_dec(v_n_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object* v_n_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Fin_instInhabited___redArg(v_n_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object* v_n_213_, lean_object* v_inst_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Fin_instInhabited(v_n_213_, v_inst_214_);
lean_dec(v_n_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_h__1_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_apply_3(v_h__1_218_, v_x_216_, lean_box(0), v_x_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(lean_object* v_n_220_, lean_object* v_motive_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_h__1_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_apply_3(v_h__1_224_, v_x_222_, lean_box(0), v_x_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(lean_object* v_n_226_, lean_object* v_motive_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_h__1_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(v_n_226_, v_motive_227_, v_x_228_, v_x_229_, v_h__1_230_);
lean_dec(v_n_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Fin_last(lean_object* v_n_232_){
_start:
{
lean_inc(v_n_232_);
return v_n_232_;
}
}
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object* v_n_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Fin_last(v_n_233_);
lean_dec(v_n_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object* v_i_235_){
_start:
{
lean_inc(v_i_235_);
return v_i_235_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object* v_i_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Fin_castLT___redArg(v_i_236_);
lean_dec(v_i_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object* v_n_238_, lean_object* v_m_239_, lean_object* v_i_240_, lean_object* v_h_241_){
_start:
{
lean_inc(v_i_240_);
return v_i_240_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object* v_n_242_, lean_object* v_m_243_, lean_object* v_i_244_, lean_object* v_h_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Fin_castLT(v_n_242_, v_m_243_, v_i_244_, v_h_245_);
lean_dec(v_i_244_);
lean_dec(v_m_243_);
lean_dec(v_n_242_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object* v_i_247_){
_start:
{
lean_inc(v_i_247_);
return v_i_247_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object* v_i_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Fin_castLE___redArg(v_i_248_);
lean_dec(v_i_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object* v_n_250_, lean_object* v_m_251_, lean_object* v_h_252_, lean_object* v_i_253_){
_start:
{
lean_inc(v_i_253_);
return v_i_253_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object* v_n_254_, lean_object* v_m_255_, lean_object* v_h_256_, lean_object* v_i_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Fin_castLE(v_n_254_, v_m_255_, v_h_256_, v_i_257_);
lean_dec(v_i_257_);
lean_dec(v_m_255_);
lean_dec(v_n_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object* v_i_259_){
_start:
{
lean_inc(v_i_259_);
return v_i_259_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object* v_i_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Fin_cast___redArg(v_i_260_);
lean_dec(v_i_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast(lean_object* v_n_262_, lean_object* v_m_263_, lean_object* v_eq_264_, lean_object* v_i_265_){
_start:
{
lean_inc(v_i_265_);
return v_i_265_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object* v_n_266_, lean_object* v_m_267_, lean_object* v_eq_268_, lean_object* v_i_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Fin_cast(v_n_266_, v_m_267_, v_eq_268_, v_i_269_);
lean_dec(v_i_269_);
lean_dec(v_m_267_);
lean_dec(v_n_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object* v_i_271_){
_start:
{
lean_inc(v_i_271_);
return v_i_271_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object* v_i_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Fin_castAdd___redArg(v_i_272_);
lean_dec(v_i_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object* v_n_274_, lean_object* v_m_275_, lean_object* v_i_276_){
_start:
{
lean_inc(v_i_276_);
return v_i_276_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object* v_n_277_, lean_object* v_m_278_, lean_object* v_i_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Fin_castAdd(v_n_277_, v_m_278_, v_i_279_);
lean_dec(v_i_279_);
lean_dec(v_m_278_);
lean_dec(v_n_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object* v_a_281_){
_start:
{
lean_inc(v_a_281_);
return v_a_281_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Fin_castSucc___redArg(v_a_282_);
lean_dec(v_a_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object* v_n_284_, lean_object* v_a_285_){
_start:
{
lean_inc(v_a_285_);
return v_a_285_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object* v_n_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Fin_castSucc(v_n_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec(v_n_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object* v_i_289_, lean_object* v_m_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_nat_add(v_i_289_, v_m_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object* v_i_292_, lean_object* v_m_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Fin_addNat___redArg(v_i_292_, v_m_293_);
lean_dec(v_m_293_);
lean_dec(v_i_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object* v_n_295_, lean_object* v_i_296_, lean_object* v_m_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_nat_add(v_i_296_, v_m_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object* v_n_299_, lean_object* v_i_300_, lean_object* v_m_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Fin_addNat(v_n_299_, v_i_300_, v_m_301_);
lean_dec(v_m_301_);
lean_dec(v_i_300_);
lean_dec(v_n_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object* v_n_303_, lean_object* v_i_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_nat_add(v_n_303_, v_i_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object* v_n_306_, lean_object* v_i_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Fin_natAdd___redArg(v_n_306_, v_i_307_);
lean_dec(v_i_307_);
lean_dec(v_n_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object* v_m_309_, lean_object* v_n_310_, lean_object* v_i_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_nat_add(v_n_310_, v_i_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object* v_m_313_, lean_object* v_n_314_, lean_object* v_i_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Fin_natAdd(v_m_313_, v_n_314_, v_i_315_);
lean_dec(v_i_315_);
lean_dec(v_n_314_);
lean_dec(v_m_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev(lean_object* v_n_317_, lean_object* v_i_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_i_318_, v___x_319_);
v___x_321_ = lean_nat_sub(v_n_317_, v___x_320_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object* v_n_322_, lean_object* v_i_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Fin_rev(v_n_322_, v_i_323_);
lean_dec(v_i_323_);
lean_dec(v_n_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object* v_m_325_, lean_object* v_i_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_nat_sub(v_i_326_, v_m_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object* v_m_328_, lean_object* v_i_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Fin_subNat___redArg(v_m_328_, v_i_329_);
lean_dec(v_i_329_);
lean_dec(v_m_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object* v_n_331_, lean_object* v_m_332_, lean_object* v_i_333_, lean_object* v_h_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_nat_sub(v_i_333_, v_m_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object* v_n_336_, lean_object* v_m_337_, lean_object* v_i_338_, lean_object* v_h_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Fin_subNat(v_n_336_, v_m_337_, v_i_338_, v_h_339_);
lean_dec(v_i_338_);
lean_dec(v_m_337_);
lean_dec(v_n_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object* v_i_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_sub(v_i_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object* v_i_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Fin_pred___redArg(v_i_344_);
lean_dec(v_i_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred(lean_object* v_n_346_, lean_object* v_i_347_, lean_object* v_h_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_sub(v_i_347_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object* v_n_351_, lean_object* v_i_352_, lean_object* v_h_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Fin_pred(v_n_351_, v_i_352_, v_h_353_);
lean_dec(v_i_352_);
lean_dec(v_n_351_);
return v_res_354_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
