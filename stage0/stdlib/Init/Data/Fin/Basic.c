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
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object*, lean_object*);
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
lean_object* l_Fin_coeToNat___redArg(){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l_Fin_coeToNat___redArg___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT void l_Fin_coeToNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Fin_coeToNat___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Fin_coeToNat___redArg();
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object* v_n_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l_Fin_coeToNat___redArg___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object* v_n_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Fin_coeToNat(v_n_12_);
lean_dec(v_n_12_);
return v_res_13_;
}
}
lean_object* l_Fin_elim0___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Fin_elim0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_15_;
v_res_15_ = l_Fin_elim0___redArg();
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Fin_elim0___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Fin_elim0___redArg();
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object* v_00_u03b1_18_, lean_object* v_x_19_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object* v_00_u03b1_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Fin_elim0(v_00_u03b1_20_, v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_add(v_x_23_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Fin_succ___redArg(v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ(lean_object* v_n_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Fin_succ___redArg(v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object* v_n_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Fin_succ(v_n_31_, v_x_32_);
lean_dec(v_x_32_);
lean_dec(v_n_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object* v_n_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_nat_mod(v_a_35_, v_n_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object* v_n_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Fin_ofNat___redArg(v_n_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec(v_n_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object* v_n_40_, lean_object* v_inst_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_nat_mod(v_a_42_, v_n_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object* v_n_44_, lean_object* v_inst_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Fin_ofNat(v_n_44_, v_inst_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec(v_n_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object* v_i_48_){
_start:
{
lean_inc(v_i_48_);
return v_i_48_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Fin_toNat___redArg(v_i_49_);
lean_dec(v_i_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object* v_n_51_, lean_object* v_i_52_){
_start:
{
lean_inc(v_i_52_);
return v_i_52_;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object* v_n_53_, lean_object* v_i_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Fin_toNat(v_n_53_, v_i_54_);
lean_dec(v_i_54_);
lean_dec(v_n_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Fin_add(lean_object* v_n_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_nat_add(v_x_57_, v_x_58_);
v___x_60_ = lean_nat_mod(v___x_59_, v_n_56_);
lean_dec(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object* v_n_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Fin_add(v_n_61_, v_x_62_, v_x_63_);
lean_dec(v_x_63_);
lean_dec(v_x_62_);
lean_dec(v_n_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul(lean_object* v_n_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_nat_mul(v_x_66_, v_x_67_);
v___x_69_ = lean_nat_mod(v___x_68_, v_n_65_);
lean_dec(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object* v_n_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Fin_mul(v_n_70_, v_x_71_, v_x_72_);
lean_dec(v_x_72_);
lean_dec(v_x_71_);
lean_dec(v_n_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub(lean_object* v_n_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_nat_sub(v_n_74_, v_x_76_);
v___x_78_ = lean_nat_add(v___x_77_, v_x_75_);
lean_dec(v___x_77_);
v___x_79_ = lean_nat_mod(v___x_78_, v_n_74_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object* v_n_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Fin_sub(v_n_80_, v_x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_x_81_);
lean_dec(v_n_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_nat_mod(v_x_84_, v_x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Fin_mod___redArg(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod(lean_object* v_n_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_nat_mod(v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object* v_n_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Fin_mod(v_n_94_, v_x_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec(v_x_95_);
lean_dec(v_n_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_nat_div(v_x_98_, v_x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Fin_div___redArg(v_x_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec(v_x_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Fin_div(lean_object* v_n_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_nat_div(v_x_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object* v_n_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Fin_div(v_n_108_, v_x_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec(v_x_109_);
lean_dec(v_n_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_nat_mod(v_x_112_, v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Fin_modn___redArg(v_x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec(v_x_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn(lean_object* v_n_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_nat_mod(v_x_119_, v_x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object* v_n_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Fin_modn(v_n_122_, v_x_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_x_123_);
lean_dec(v_n_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Fin_land(lean_object* v_n_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_nat_land(v_x_127_, v_x_128_);
v___x_130_ = lean_nat_mod(v___x_129_, v_n_126_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object* v_n_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Fin_land(v_n_131_, v_x_132_, v_x_133_);
lean_dec(v_x_133_);
lean_dec(v_x_132_);
lean_dec(v_n_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor(lean_object* v_n_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_lor(v_x_136_, v_x_137_);
v___x_139_ = lean_nat_mod(v___x_138_, v_n_135_);
lean_dec(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object* v_n_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Fin_lor(v_n_140_, v_x_141_, v_x_142_);
lean_dec(v_x_142_);
lean_dec(v_x_141_);
lean_dec(v_n_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor(lean_object* v_n_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_nat_lxor(v_x_145_, v_x_146_);
v___x_148_ = lean_nat_mod(v___x_147_, v_n_144_);
lean_dec(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object* v_n_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Fin_xor(v_n_149_, v_x_150_, v_x_151_);
lean_dec(v_x_151_);
lean_dec(v_x_150_);
lean_dec(v_n_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object* v_n_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_nat_shiftl(v_x_154_, v_x_155_);
v___x_157_ = lean_nat_mod(v___x_156_, v_n_153_);
lean_dec(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object* v_n_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Fin_shiftLeft(v_n_158_, v_x_159_, v_x_160_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
lean_dec(v_n_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object* v_n_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_nat_shiftr(v_x_163_, v_x_164_);
v___x_166_ = lean_nat_mod(v___x_165_, v_n_162_);
lean_dec(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object* v_n_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Fin_shiftRight(v_n_167_, v_x_168_, v_x_169_);
lean_dec(v_x_169_);
lean_dec(v_x_168_);
lean_dec(v_n_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(v___x_172_, 0, v_n_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object* v_n_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(v___x_174_, 0, v_n_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object* v_n_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(v___x_176_, 0, v_n_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object* v_n_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_closure((void*)(l_Fin_mod___boxed), 3, 1);
lean_closure_set(v___x_178_, 0, v_n_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object* v_n_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_closure((void*)(l_Fin_div___boxed), 3, 1);
lean_closure_set(v___x_180_, 0, v_n_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object* v_n_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_closure((void*)(l_Fin_land___boxed), 3, 1);
lean_closure_set(v___x_182_, 0, v_n_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object* v_n_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_closure((void*)(l_Fin_lor___boxed), 3, 1);
lean_closure_set(v___x_184_, 0, v_n_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Fin_instXorOp(lean_object* v_n_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_closure((void*)(l_Fin_xor___boxed), 3, 1);
lean_closure_set(v___x_186_, 0, v_n_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object* v_n_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_closure((void*)(l_Fin_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_188_, 0, v_n_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object* v_n_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_closure((void*)(l_Fin_shiftRight___boxed), 3, 1);
lean_closure_set(v___x_190_, 0, v_n_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object* v_n_191_, lean_object* v_i_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_nat_mod(v_i_192_, v_n_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object* v_n_194_, lean_object* v_i_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Fin_instOfNat___redArg(v_n_194_, v_i_195_);
lean_dec(v_i_195_);
lean_dec(v_n_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object* v_n_197_, lean_object* v_inst_198_, lean_object* v_i_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_nat_mod(v_i_199_, v_n_197_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object* v_n_201_, lean_object* v_inst_202_, lean_object* v_i_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Fin_instOfNat(v_n_201_, v_inst_202_, v_i_203_);
lean_dec(v_i_203_);
lean_dec(v_n_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object* v_n_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_nat_sub(v_n_205_, v_a_206_);
v___x_208_ = lean_nat_mod(v___x_207_, v_n_205_);
lean_dec(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object* v_n_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Fin_neg___lam__0(v_n_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec(v_n_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Fin_neg(lean_object* v_n_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_213_, 0, v_n_212_);
return v___f_213_;
}
}
lean_object* l_Fin_instInhabited___redArg(){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
return v___x_215_;
}
}
LEAN_EXPORT void l_Fin_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_216_;
v_res_216_ = l_Fin_instInhabited___redArg();
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object* v___dummy_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Fin_instInhabited___redArg();
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object* v_n_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(0u);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object* v_n_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Fin_instInhabited(v_n_222_, v_inst_223_);
lean_dec(v_n_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Fin_last(lean_object* v_n_225_){
_start:
{
lean_inc(v_n_225_);
return v_n_225_;
}
}
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object* v_n_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Fin_last(v_n_226_);
lean_dec(v_n_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object* v_i_228_){
_start:
{
lean_inc(v_i_228_);
return v_i_228_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object* v_i_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Fin_castLT___redArg(v_i_229_);
lean_dec(v_i_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object* v_n_231_, lean_object* v_m_232_, lean_object* v_i_233_, lean_object* v_h_234_){
_start:
{
lean_inc(v_i_233_);
return v_i_233_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object* v_n_235_, lean_object* v_m_236_, lean_object* v_i_237_, lean_object* v_h_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Fin_castLT(v_n_235_, v_m_236_, v_i_237_, v_h_238_);
lean_dec(v_i_237_);
lean_dec(v_m_236_);
lean_dec(v_n_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object* v_i_240_){
_start:
{
lean_inc(v_i_240_);
return v_i_240_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object* v_i_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Fin_castLE___redArg(v_i_241_);
lean_dec(v_i_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object* v_n_243_, lean_object* v_m_244_, lean_object* v_h_245_, lean_object* v_i_246_){
_start:
{
lean_inc(v_i_246_);
return v_i_246_;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object* v_n_247_, lean_object* v_m_248_, lean_object* v_h_249_, lean_object* v_i_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Fin_castLE(v_n_247_, v_m_248_, v_h_249_, v_i_250_);
lean_dec(v_i_250_);
lean_dec(v_m_248_);
lean_dec(v_n_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object* v_i_252_){
_start:
{
lean_inc(v_i_252_);
return v_i_252_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object* v_i_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Fin_cast___redArg(v_i_253_);
lean_dec(v_i_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast(lean_object* v_n_255_, lean_object* v_m_256_, lean_object* v_eq_257_, lean_object* v_i_258_){
_start:
{
lean_inc(v_i_258_);
return v_i_258_;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object* v_n_259_, lean_object* v_m_260_, lean_object* v_eq_261_, lean_object* v_i_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Fin_cast(v_n_259_, v_m_260_, v_eq_261_, v_i_262_);
lean_dec(v_i_262_);
lean_dec(v_m_260_);
lean_dec(v_n_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object* v_i_264_){
_start:
{
lean_inc(v_i_264_);
return v_i_264_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object* v_i_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Fin_castAdd___redArg(v_i_265_);
lean_dec(v_i_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object* v_n_267_, lean_object* v_m_268_, lean_object* v_i_269_){
_start:
{
lean_inc(v_i_269_);
return v_i_269_;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object* v_n_270_, lean_object* v_m_271_, lean_object* v_i_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Fin_castAdd(v_n_270_, v_m_271_, v_i_272_);
lean_dec(v_i_272_);
lean_dec(v_m_271_);
lean_dec(v_n_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object* v_a_274_){
_start:
{
lean_inc(v_a_274_);
return v_a_274_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Fin_castSucc___redArg(v_a_275_);
lean_dec(v_a_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object* v_n_277_, lean_object* v_a_278_){
_start:
{
lean_inc(v_a_278_);
return v_a_278_;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object* v_n_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Fin_castSucc(v_n_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec(v_n_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object* v_i_282_, lean_object* v_m_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_nat_add(v_i_282_, v_m_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object* v_i_285_, lean_object* v_m_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Fin_addNat___redArg(v_i_285_, v_m_286_);
lean_dec(v_m_286_);
lean_dec(v_i_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object* v_n_288_, lean_object* v_i_289_, lean_object* v_m_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_nat_add(v_i_289_, v_m_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object* v_n_292_, lean_object* v_i_293_, lean_object* v_m_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Fin_addNat(v_n_292_, v_i_293_, v_m_294_);
lean_dec(v_m_294_);
lean_dec(v_i_293_);
lean_dec(v_n_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object* v_n_296_, lean_object* v_i_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_nat_add(v_n_296_, v_i_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object* v_n_299_, lean_object* v_i_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Fin_natAdd___redArg(v_n_299_, v_i_300_);
lean_dec(v_i_300_);
lean_dec(v_n_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object* v_m_302_, lean_object* v_n_303_, lean_object* v_i_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_nat_add(v_n_303_, v_i_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object* v_m_306_, lean_object* v_n_307_, lean_object* v_i_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Fin_natAdd(v_m_306_, v_n_307_, v_i_308_);
lean_dec(v_i_308_);
lean_dec(v_n_307_);
lean_dec(v_m_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev(lean_object* v_n_310_, lean_object* v_i_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_i_311_, v___x_312_);
v___x_314_ = lean_nat_sub(v_n_310_, v___x_313_);
lean_dec(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object* v_n_315_, lean_object* v_i_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Fin_rev(v_n_315_, v_i_316_);
lean_dec(v_i_316_);
lean_dec(v_n_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object* v_m_318_, lean_object* v_i_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_nat_sub(v_i_319_, v_m_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object* v_m_321_, lean_object* v_i_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Fin_subNat___redArg(v_m_321_, v_i_322_);
lean_dec(v_i_322_);
lean_dec(v_m_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object* v_n_324_, lean_object* v_m_325_, lean_object* v_i_326_, lean_object* v_h_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_nat_sub(v_i_326_, v_m_325_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object* v_n_329_, lean_object* v_m_330_, lean_object* v_i_331_, lean_object* v_h_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Fin_subNat(v_n_329_, v_m_330_, v_i_331_, v_h_332_);
lean_dec(v_i_331_);
lean_dec(v_m_330_);
lean_dec(v_n_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object* v_i_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_sub(v_i_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object* v_i_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Fin_pred___redArg(v_i_337_);
lean_dec(v_i_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred(lean_object* v_n_339_, lean_object* v_i_340_, lean_object* v_h_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_sub(v_i_340_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object* v_n_344_, lean_object* v_i_345_, lean_object* v_h_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Fin_pred(v_n_344_, v_i_345_, v_h_346_);
lean_dec(v_i_345_);
lean_dec(v_n_344_);
return v_res_347_;
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
