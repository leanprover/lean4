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
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Fin_coeToNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_coeToNat___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_coeToNat___redArg___closed__0 = (const lean_object*)&l_Fin_coeToNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg();
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_elim0___redArg();
LEAN_EXPORT lean_object* l_Fin_elim0___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___lam__0(lean_object* v_v_1_){
_start:
{
lean_inc(v_v_1_);
return v_v_1_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___lam__0___boxed(lean_object* v_v_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Fin_coeToNat___redArg___lam__0(v_v_2_);
lean_dec(v_v_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg(){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l_Fin_coeToNat___redArg___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Fin_coeToNat___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object* v_n_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l_Fin_coeToNat___redArg___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object* v_n_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Fin_coeToNat(v_n_11_);
lean_dec(v_n_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___redArg___boxed(lean_object* v___dummy_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Fin_elim0___redArg();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object* v_00_u03b1_16_, lean_object* v_x_17_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object* v_00_u03b1_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Fin_elim0(v_00_u03b1_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_add(v_x_21_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Fin_succ___redArg(v_x_24_);
lean_dec(v_x_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ(lean_object* v_n_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Fin_succ___redArg(v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object* v_n_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Fin_succ(v_n_29_, v_x_30_);
lean_dec(v_x_30_);
lean_dec(v_n_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object* v_n_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_nat_mod(v_a_33_, v_n_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object* v_n_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Fin_ofNat___redArg(v_n_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec(v_n_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object* v_n_38_, lean_object* v_inst_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_nat_mod(v_a_40_, v_n_38_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object* v_n_42_, lean_object* v_inst_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Fin_ofNat(v_n_42_, v_inst_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec(v_n_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object* v_i_46_){
_start:
{
lean_inc(v_i_46_);
return v_i_46_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object* v_i_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Fin_toNat___redArg(v_i_47_);
lean_dec(v_i_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object* v_n_49_, lean_object* v_i_50_){
_start:
{
lean_inc(v_i_50_);
return v_i_50_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object* v_n_51_, lean_object* v_i_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Fin_toNat(v_n_51_, v_i_52_);
lean_dec(v_i_52_);
lean_dec(v_n_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Fin_add(lean_object* v_n_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_nat_add(v_x_55_, v_x_56_);
v___x_58_ = lean_nat_mod(v___x_57_, v_n_54_);
lean_dec(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object* v_n_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Fin_add(v_n_59_, v_x_60_, v_x_61_);
lean_dec(v_x_61_);
lean_dec(v_x_60_);
lean_dec(v_n_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul(lean_object* v_n_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_nat_mul(v_x_64_, v_x_65_);
v___x_67_ = lean_nat_mod(v___x_66_, v_n_63_);
lean_dec(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object* v_n_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Fin_mul(v_n_68_, v_x_69_, v_x_70_);
lean_dec(v_x_70_);
lean_dec(v_x_69_);
lean_dec(v_n_68_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub(lean_object* v_n_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_nat_sub(v_n_72_, v_x_74_);
v___x_76_ = lean_nat_add(v___x_75_, v_x_73_);
lean_dec(v___x_75_);
v___x_77_ = lean_nat_mod(v___x_76_, v_n_72_);
lean_dec(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object* v_n_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Fin_sub(v_n_78_, v_x_79_, v_x_80_);
lean_dec(v_x_80_);
lean_dec(v_x_79_);
lean_dec(v_n_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_nat_mod(v_x_82_, v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Fin_mod___redArg(v_x_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec(v_x_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod(lean_object* v_n_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_nat_mod(v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object* v_n_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Fin_mod(v_n_92_, v_x_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec(v_x_93_);
lean_dec(v_n_92_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_nat_div(v_x_96_, v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Fin_div___redArg(v_x_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec(v_x_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Fin_div(lean_object* v_n_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_nat_div(v_x_103_, v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object* v_n_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Fin_div(v_n_106_, v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
lean_dec(v_n_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_nat_mod(v_x_110_, v_x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Fin_modn___redArg(v_x_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v_x_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn(lean_object* v_n_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_nat_mod(v_x_117_, v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object* v_n_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Fin_modn(v_n_120_, v_x_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec(v_x_121_);
lean_dec(v_n_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Fin_land(lean_object* v_n_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_nat_land(v_x_125_, v_x_126_);
v___x_128_ = lean_nat_mod(v___x_127_, v_n_124_);
lean_dec(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object* v_n_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Fin_land(v_n_129_, v_x_130_, v_x_131_);
lean_dec(v_x_131_);
lean_dec(v_x_130_);
lean_dec(v_n_129_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor(lean_object* v_n_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_nat_lor(v_x_134_, v_x_135_);
v___x_137_ = lean_nat_mod(v___x_136_, v_n_133_);
lean_dec(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object* v_n_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Fin_lor(v_n_138_, v_x_139_, v_x_140_);
lean_dec(v_x_140_);
lean_dec(v_x_139_);
lean_dec(v_n_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor(lean_object* v_n_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_nat_lxor(v_x_143_, v_x_144_);
v___x_146_ = lean_nat_mod(v___x_145_, v_n_142_);
lean_dec(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object* v_n_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Fin_xor(v_n_147_, v_x_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec(v_x_148_);
lean_dec(v_n_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object* v_n_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_nat_shiftl(v_x_152_, v_x_153_);
v___x_155_ = lean_nat_mod(v___x_154_, v_n_151_);
lean_dec(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object* v_n_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Fin_shiftLeft(v_n_156_, v_x_157_, v_x_158_);
lean_dec(v_x_158_);
lean_dec(v_x_157_);
lean_dec(v_n_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object* v_n_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_nat_shiftr(v_x_161_, v_x_162_);
v___x_164_ = lean_nat_mod(v___x_163_, v_n_160_);
lean_dec(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object* v_n_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Fin_shiftRight(v_n_165_, v_x_166_, v_x_167_);
lean_dec(v_x_167_);
lean_dec(v_x_166_);
lean_dec(v_n_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object* v_n_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(v___x_170_, 0, v_n_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(v___x_172_, 0, v_n_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object* v_n_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_174_, 0, v_n_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object* v_n_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_closure((void*)(l_Fin_mod___boxed), 3, 1);
lean_closure_set(v___x_176_, 0, v_n_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object* v_n_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_closure((void*)(l_Fin_div___boxed), 3, 1);
lean_closure_set(v___x_178_, 0, v_n_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object* v_n_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_closure((void*)(l_Fin_land___boxed), 3, 1);
lean_closure_set(v___x_180_, 0, v_n_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object* v_n_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_closure((void*)(l_Fin_lor___boxed), 3, 1);
lean_closure_set(v___x_182_, 0, v_n_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Fin_instXorOp(lean_object* v_n_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_closure((void*)(l_Fin_xor___boxed), 3, 1);
lean_closure_set(v___x_184_, 0, v_n_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object* v_n_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_closure((void*)(l_Fin_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_186_, 0, v_n_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object* v_n_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_closure((void*)(l_Fin_shiftRight___boxed), 3, 1);
lean_closure_set(v___x_188_, 0, v_n_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object* v_n_189_, lean_object* v_i_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_nat_mod(v_i_190_, v_n_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object* v_n_192_, lean_object* v_i_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Fin_instOfNat___redArg(v_n_192_, v_i_193_);
lean_dec(v_i_193_);
lean_dec(v_n_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object* v_n_195_, lean_object* v_inst_196_, lean_object* v_i_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_nat_mod(v_i_197_, v_n_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object* v_n_199_, lean_object* v_inst_200_, lean_object* v_i_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Fin_instOfNat(v_n_199_, v_inst_200_, v_i_201_);
lean_dec(v_i_201_);
lean_dec(v_n_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object* v_n_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_nat_sub(v_n_203_, v_a_204_);
v___x_206_ = lean_nat_mod(v___x_205_, v_n_203_);
lean_dec(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object* v_n_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Fin_neg___lam__0(v_n_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec(v_n_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg(lean_object* v_n_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_211_, 0, v_n_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg(lean_object* v_n_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_mod(v___x_213_, v_n_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object* v_n_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Fin_instInhabited___redArg(v_n_215_);
lean_dec(v_n_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object* v_n_217_, lean_object* v_inst_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Fin_instInhabited___redArg(v_n_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object* v_n_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Fin_instInhabited(v_n_220_, v_inst_221_);
lean_dec(v_n_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(lean_object* v_x_223_, lean_object* v_x_224_, lean_object* v_h__1_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_apply_3(v_h__1_225_, v_x_223_, lean_box(0), v_x_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(lean_object* v_n_227_, lean_object* v_motive_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_h__1_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_apply_3(v_h__1_231_, v_x_229_, lean_box(0), v_x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(lean_object* v_n_233_, lean_object* v_motive_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_h__1_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(v_n_233_, v_motive_234_, v_x_235_, v_x_236_, v_h__1_237_);
lean_dec(v_n_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Fin_last(lean_object* v_n_239_){
_start:
{
lean_inc(v_n_239_);
return v_n_239_;
}
}
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object* v_n_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Fin_last(v_n_240_);
lean_dec(v_n_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object* v_i_242_){
_start:
{
lean_inc(v_i_242_);
return v_i_242_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object* v_i_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Fin_castLT___redArg(v_i_243_);
lean_dec(v_i_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object* v_n_245_, lean_object* v_m_246_, lean_object* v_i_247_, lean_object* v_h_248_){
_start:
{
lean_inc(v_i_247_);
return v_i_247_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object* v_n_249_, lean_object* v_m_250_, lean_object* v_i_251_, lean_object* v_h_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Fin_castLT(v_n_249_, v_m_250_, v_i_251_, v_h_252_);
lean_dec(v_i_251_);
lean_dec(v_m_250_);
lean_dec(v_n_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object* v_i_254_){
_start:
{
lean_inc(v_i_254_);
return v_i_254_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object* v_i_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Fin_castLE___redArg(v_i_255_);
lean_dec(v_i_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object* v_n_257_, lean_object* v_m_258_, lean_object* v_h_259_, lean_object* v_i_260_){
_start:
{
lean_inc(v_i_260_);
return v_i_260_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object* v_n_261_, lean_object* v_m_262_, lean_object* v_h_263_, lean_object* v_i_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Fin_castLE(v_n_261_, v_m_262_, v_h_263_, v_i_264_);
lean_dec(v_i_264_);
lean_dec(v_m_262_);
lean_dec(v_n_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object* v_i_266_){
_start:
{
lean_inc(v_i_266_);
return v_i_266_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object* v_i_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Fin_cast___redArg(v_i_267_);
lean_dec(v_i_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast(lean_object* v_n_269_, lean_object* v_m_270_, lean_object* v_eq_271_, lean_object* v_i_272_){
_start:
{
lean_inc(v_i_272_);
return v_i_272_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object* v_n_273_, lean_object* v_m_274_, lean_object* v_eq_275_, lean_object* v_i_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Fin_cast(v_n_273_, v_m_274_, v_eq_275_, v_i_276_);
lean_dec(v_i_276_);
lean_dec(v_m_274_);
lean_dec(v_n_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object* v_i_278_){
_start:
{
lean_inc(v_i_278_);
return v_i_278_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object* v_i_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Fin_castAdd___redArg(v_i_279_);
lean_dec(v_i_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object* v_n_281_, lean_object* v_m_282_, lean_object* v_i_283_){
_start:
{
lean_inc(v_i_283_);
return v_i_283_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object* v_n_284_, lean_object* v_m_285_, lean_object* v_i_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Fin_castAdd(v_n_284_, v_m_285_, v_i_286_);
lean_dec(v_i_286_);
lean_dec(v_m_285_);
lean_dec(v_n_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object* v_a_288_){
_start:
{
lean_inc(v_a_288_);
return v_a_288_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Fin_castSucc___redArg(v_a_289_);
lean_dec(v_a_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object* v_n_291_, lean_object* v_a_292_){
_start:
{
lean_inc(v_a_292_);
return v_a_292_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object* v_n_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Fin_castSucc(v_n_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec(v_n_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object* v_i_296_, lean_object* v_m_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_nat_add(v_i_296_, v_m_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object* v_i_299_, lean_object* v_m_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Fin_addNat___redArg(v_i_299_, v_m_300_);
lean_dec(v_m_300_);
lean_dec(v_i_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object* v_n_302_, lean_object* v_i_303_, lean_object* v_m_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_nat_add(v_i_303_, v_m_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object* v_n_306_, lean_object* v_i_307_, lean_object* v_m_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Fin_addNat(v_n_306_, v_i_307_, v_m_308_);
lean_dec(v_m_308_);
lean_dec(v_i_307_);
lean_dec(v_n_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object* v_n_310_, lean_object* v_i_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_nat_add(v_n_310_, v_i_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object* v_n_313_, lean_object* v_i_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Fin_natAdd___redArg(v_n_313_, v_i_314_);
lean_dec(v_i_314_);
lean_dec(v_n_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object* v_m_316_, lean_object* v_n_317_, lean_object* v_i_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_nat_add(v_n_317_, v_i_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object* v_m_320_, lean_object* v_n_321_, lean_object* v_i_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Fin_natAdd(v_m_320_, v_n_321_, v_i_322_);
lean_dec(v_i_322_);
lean_dec(v_n_321_);
lean_dec(v_m_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev(lean_object* v_n_324_, lean_object* v_i_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v_i_325_, v___x_326_);
v___x_328_ = lean_nat_sub(v_n_324_, v___x_327_);
lean_dec(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object* v_n_329_, lean_object* v_i_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Fin_rev(v_n_329_, v_i_330_);
lean_dec(v_i_330_);
lean_dec(v_n_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object* v_m_332_, lean_object* v_i_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_nat_sub(v_i_333_, v_m_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object* v_m_335_, lean_object* v_i_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Fin_subNat___redArg(v_m_335_, v_i_336_);
lean_dec(v_i_336_);
lean_dec(v_m_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object* v_n_338_, lean_object* v_m_339_, lean_object* v_i_340_, lean_object* v_h_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_nat_sub(v_i_340_, v_m_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object* v_n_343_, lean_object* v_m_344_, lean_object* v_i_345_, lean_object* v_h_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Fin_subNat(v_n_343_, v_m_344_, v_i_345_, v_h_346_);
lean_dec(v_i_345_);
lean_dec(v_m_344_);
lean_dec(v_n_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object* v_i_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_sub(v_i_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object* v_i_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Fin_pred___redArg(v_i_351_);
lean_dec(v_i_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred(lean_object* v_n_353_, lean_object* v_i_354_, lean_object* v_h_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_sub(v_i_354_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object* v_n_358_, lean_object* v_i_359_, lean_object* v_h_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Fin_pred(v_n_358_, v_i_359_, v_h_360_);
lean_dec(v_i_359_);
lean_dec(v_n_358_);
return v_res_361_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
