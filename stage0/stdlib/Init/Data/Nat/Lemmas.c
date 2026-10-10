// Lean compiler output
// Module: Init.Data.Nat.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.Nat.Log2 import all Init.Data.Nat.Log2 import Init.TacticsExtra public import Init.Data.Nat.Div.Basic public import Init.PropLemmas import Init.ByCases import Init.Data.Nat.Dvd import Init.Data.Nat.Internal.Linear import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Omega import Init.RCases
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_allLTTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allLTTR___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyLTTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyLTTR___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(lean_object* v_n_1_, lean_object* v_f_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_i_3_);
lean_dec_ref(v_f_2_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_i_3_, v_one_6_);
lean_dec(v_i_3_);
v___x_8_ = lean_nat_add(v_n_7_, v_one_6_);
v___x_9_ = lean_nat_sub(v_n_1_, v___x_8_);
lean_dec(v___x_8_);
lean_inc_ref(v_f_2_);
v___x_10_ = lean_apply_2(v_f_2_, v___x_9_, lean_box(0));
v___x_11_ = lean_unbox(v___x_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
lean_dec(v_n_7_);
lean_dec_ref(v_f_2_);
v___x_12_ = lean_unbox(v___x_10_);
return v___x_12_;
}
else
{
v_i_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1_ = stack[0].m_obj;
lean_object* v_f_2_ = stack[1].m_obj;
lean_object* v_i_3_ = stack[2].m_obj;
uint8_t v_res_14_;
v_res_14_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_1_, v_f_2_, v_i_3_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg___boxed(lean_object* v_n_15_, lean_object* v_f_16_, lean_object* v_i_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_15_, v_f_16_, v_i_17_);
lean_dec(v_n_15_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object* v_n_20_, lean_object* v_f_21_, lean_object* v_i_22_, lean_object* v_a_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_20_, v_f_21_, v_i_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_20_ = stack[0].m_obj;
lean_object* v_f_21_ = stack[1].m_obj;
lean_object* v_i_22_ = stack[2].m_obj;
uint8_t v_res_25_;
v_res_25_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v_n_20_, v_f_21_, v_i_22_, lean_box(0));
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___boxed(lean_object* v_n_26_, lean_object* v_f_27_, lean_object* v_i_28_, lean_object* v_a_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v_n_26_, v_f_27_, v_i_28_, v_a_29_);
lean_dec(v_n_26_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
uint8_t l_Nat_allLTTR(lean_object* v_n_32_, lean_object* v_f_33_){
_start:
{
uint8_t v___x_34_; 
lean_inc(v_n_32_);
v___x_34_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_32_, v_f_33_, v_n_32_);
lean_dec(v_n_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Nat_allLTTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_32_ = stack[0].m_obj;
lean_object* v_f_33_ = stack[1].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_Nat_allLTTR(v_n_32_, v_f_33_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Nat_allLTTR___boxed(lean_object* v_n_36_, lean_object* v_f_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Nat_allLTTR(v_n_36_, v_f_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(lean_object* v_n_40_, lean_object* v_f_41_, lean_object* v_i_42_){
_start:
{
lean_object* v_zero_43_; uint8_t v_isZero_44_; 
v_zero_43_ = lean_unsigned_to_nat(0u);
v_isZero_44_ = lean_nat_dec_eq(v_i_42_, v_zero_43_);
if (v_isZero_44_ == 1)
{
uint8_t v___x_45_; 
lean_dec(v_i_42_);
lean_dec_ref(v_f_41_);
v___x_45_ = 0;
return v___x_45_;
}
else
{
lean_object* v_one_46_; lean_object* v_n_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_one_46_ = lean_unsigned_to_nat(1u);
v_n_47_ = lean_nat_sub(v_i_42_, v_one_46_);
lean_dec(v_i_42_);
v___x_48_ = lean_nat_add(v_n_47_, v_one_46_);
v___x_49_ = lean_nat_sub(v_n_40_, v___x_48_);
lean_dec(v___x_48_);
lean_inc_ref(v_f_41_);
v___x_50_ = lean_apply_2(v_f_41_, v___x_49_, lean_box(0));
v___x_51_ = lean_unbox(v___x_50_);
if (v___x_51_ == 0)
{
v_i_42_ = v_n_47_;
goto _start;
}
else
{
uint8_t v___x_53_; 
lean_dec(v_n_47_);
lean_dec_ref(v_f_41_);
v___x_53_ = lean_unbox(v___x_50_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_40_ = stack[0].m_obj;
lean_object* v_f_41_ = stack[1].m_obj;
lean_object* v_i_42_ = stack[2].m_obj;
uint8_t v_res_54_;
v_res_54_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_40_, v_f_41_, v_i_42_);
stack->m_num = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg___boxed(lean_object* v_n_55_, lean_object* v_f_56_, lean_object* v_i_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_55_, v_f_56_, v_i_57_);
lean_dec(v_n_55_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object* v_n_60_, lean_object* v_f_61_, lean_object* v_i_62_, lean_object* v_a_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_60_, v_f_61_, v_i_62_);
return v___x_64_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_60_ = stack[0].m_obj;
lean_object* v_f_61_ = stack[1].m_obj;
lean_object* v_i_62_ = stack[2].m_obj;
uint8_t v_res_65_;
v_res_65_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_60_, v_f_61_, v_i_62_, lean_box(0));
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___boxed(lean_object* v_n_66_, lean_object* v_f_67_, lean_object* v_i_68_, lean_object* v_a_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_66_, v_f_67_, v_i_68_, v_a_69_);
lean_dec(v_n_66_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l_Nat_anyLTTR(lean_object* v_n_72_, lean_object* v_f_73_){
_start:
{
uint8_t v___x_74_; 
lean_inc(v_n_72_);
v___x_74_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_72_, v_f_73_, v_n_72_);
lean_dec(v_n_72_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Nat_anyLTTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_72_ = stack[0].m_obj;
lean_object* v_f_73_ = stack[1].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Nat_anyLTTR(v_n_72_, v_f_73_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Nat_anyLTTR___boxed(lean_object* v_n_76_, lean_object* v_f_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Nat_anyLTTR(v_n_76_, v_f_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
uint8_t l_Nat_decidableBallLTTR___redArg___lam__0(lean_object* v_inst_80_, lean_object* v_i_81_, lean_object* v_h_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_apply_2(v_inst_80_, v_i_81_, lean_box(0));
v___x_84_ = lean_unbox(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT void l_Nat_decidableBallLTTR___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_80_ = stack[0].m_obj;
lean_object* v_i_81_ = stack[1].m_obj;
uint8_t v_res_85_;
v_res_85_ = l_Nat_decidableBallLTTR___redArg___lam__0(v_inst_80_, v_i_81_, lean_box(0));
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___lam__0___boxed(lean_object* v_inst_86_, lean_object* v_i_87_, lean_object* v_h_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Nat_decidableBallLTTR___redArg___lam__0(v_inst_86_, v_i_87_, v_h_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_Nat_decidableBallLTTR___redArg(lean_object* v_n_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___f_93_; uint8_t v___x_94_; 
v___f_93_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_93_, 0, v_inst_92_);
lean_inc(v_n_91_);
v___x_94_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_91_, v___f_93_, v_n_91_);
lean_dec(v_n_91_);
return v___x_94_;
}
}
LEAN_EXPORT void l_Nat_decidableBallLTTR___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_91_ = stack[0].m_obj;
lean_object* v_inst_92_ = stack[1].m_obj;
uint8_t v_res_95_;
v_res_95_ = l_Nat_decidableBallLTTR___redArg(v_n_91_, v_inst_92_);
stack->m_num = v_res_95_;
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___boxed(lean_object* v_n_96_, lean_object* v_inst_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Nat_decidableBallLTTR___redArg(v_n_96_, v_inst_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
uint8_t l_Nat_decidableBallLTTR(lean_object* v_n_100_, lean_object* v_P_101_, lean_object* v_inst_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Nat_decidableBallLTTR___redArg(v_n_100_, v_inst_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Nat_decidableBallLTTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_100_ = stack[0].m_obj;
lean_object* v_inst_102_ = stack[2].m_obj;
uint8_t v_res_104_;
v_res_104_ = l_Nat_decidableBallLTTR(v_n_100_, lean_box(0), v_inst_102_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___boxed(lean_object* v_n_105_, lean_object* v_P_106_, lean_object* v_inst_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Nat_decidableBallLTTR(v_n_105_, v_P_106_, v_inst_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object* v_inst_110_, lean_object* v_i_111_, lean_object* v_h_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_apply_1(v_inst_110_, v_i_111_);
v___x_114_ = lean_unbox(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT void l_Nat_decidableForallFin___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_110_ = stack[0].m_obj;
lean_object* v_i_111_ = stack[1].m_obj;
uint8_t v_res_115_;
v_res_115_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_110_, v_i_111_, lean_box(0));
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object* v_inst_116_, lean_object* v_i_117_, lean_object* v_h_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_116_, v_i_117_, v_h_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
uint8_t l_Nat_decidableForallFin___redArg(lean_object* v_n_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___f_123_; uint8_t v___x_124_; 
v___f_123_ = lean_alloc_closure((void*)(l_Nat_decidableForallFin___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_123_, 0, v_inst_122_);
lean_inc(v_n_121_);
v___x_124_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_121_, v___f_123_, v_n_121_);
lean_dec(v_n_121_);
return v___x_124_;
}
}
LEAN_EXPORT void l_Nat_decidableForallFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_121_ = stack[0].m_obj;
lean_object* v_inst_122_ = stack[1].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Nat_decidableForallFin___redArg(v_n_121_, v_inst_122_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object* v_n_126_, lean_object* v_inst_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Nat_decidableForallFin___redArg(v_n_126_, v_inst_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
uint8_t l_Nat_decidableForallFin(lean_object* v_n_130_, lean_object* v_P_131_, lean_object* v_inst_132_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = l_Nat_decidableForallFin___redArg(v_n_130_, v_inst_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Nat_decidableForallFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_130_ = stack[0].m_obj;
lean_object* v_inst_132_ = stack[2].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_Nat_decidableForallFin(v_n_130_, lean_box(0), v_inst_132_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object* v_n_135_, lean_object* v_P_136_, lean_object* v_inst_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Nat_decidableForallFin(v_n_135_, v_P_136_, v_inst_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
uint8_t l_Nat_decidableBallLE___redArg(lean_object* v_n_140_, lean_object* v_inst_141_){
_start:
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___f_142_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_142_, 0, v_inst_141_);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_n_140_, v___x_143_);
lean_inc(v___x_144_);
v___x_145_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v___x_144_, v___f_142_, v___x_144_);
lean_dec(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT void l_Nat_decidableBallLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_140_ = stack[0].m_obj;
lean_object* v_inst_141_ = stack[1].m_obj;
uint8_t v_res_146_;
v_res_146_ = l_Nat_decidableBallLE___redArg(v_n_140_, v_inst_141_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object* v_n_147_, lean_object* v_inst_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Nat_decidableBallLE___redArg(v_n_147_, v_inst_148_);
lean_dec(v_n_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
uint8_t l_Nat_decidableBallLE(lean_object* v_n_151_, lean_object* v_P_152_, lean_object* v_inst_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Nat_decidableBallLE___redArg(v_n_151_, v_inst_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Nat_decidableBallLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_151_ = stack[0].m_obj;
lean_object* v_inst_153_ = stack[2].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Nat_decidableBallLE(v_n_151_, lean_box(0), v_inst_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object* v_n_156_, lean_object* v_P_157_, lean_object* v_inst_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Nat_decidableBallLE(v_n_156_, v_P_157_, v_inst_158_);
lean_dec(v_n_156_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object* v_inst_161_, lean_object* v_i_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_apply_1(v_inst_161_, v_i_162_);
v___x_165_ = lean_unbox(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLTTR___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_161_ = stack[0].m_obj;
lean_object* v_i_162_ = stack[1].m_obj;
uint8_t v_res_166_;
v_res_166_ = l_Nat_decidableExistsLTTR___redArg___lam__0(v_inst_161_, v_i_162_, lean_box(0));
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object* v_inst_167_, lean_object* v_i_168_, lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Nat_decidableExistsLTTR___redArg___lam__0(v_inst_167_, v_i_168_, v_x_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object* v_inst_172_, lean_object* v_n_173_){
_start:
{
lean_object* v___f_174_; uint8_t v___x_175_; 
v___f_174_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_174_, 0, v_inst_172_);
lean_inc(v_n_173_);
v___x_175_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_173_, v___f_174_, v_n_173_);
lean_dec(v_n_173_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLTTR___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_172_ = stack[0].m_obj;
lean_object* v_n_173_ = stack[1].m_obj;
uint8_t v_res_176_;
v_res_176_ = l_Nat_decidableExistsLTTR___redArg(v_inst_172_, v_n_173_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object* v_inst_177_, lean_object* v_n_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Nat_decidableExistsLTTR___redArg(v_inst_177_, v_n_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
uint8_t l_Nat_decidableExistsLTTR(lean_object* v_p_181_, lean_object* v_inst_182_, lean_object* v_n_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l_Nat_decidableExistsLTTR___redArg(v_inst_182_, v_n_183_);
return v___x_184_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLTTR_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_182_ = stack[1].m_obj;
lean_object* v_n_183_ = stack[2].m_obj;
uint8_t v_res_185_;
v_res_185_ = l_Nat_decidableExistsLTTR(lean_box(0), v_inst_182_, v_n_183_);
stack->m_num = v_res_185_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object* v_p_186_, lean_object* v_inst_187_, lean_object* v_n_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Nat_decidableExistsLTTR(v_p_186_, v_inst_187_, v_n_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Nat_decidableExistsLE___redArg(lean_object* v_inst_191_, lean_object* v_n_192_){
_start:
{
lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___f_193_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_193_, 0, v_inst_191_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_n_192_, v___x_194_);
lean_inc(v___x_195_);
v___x_196_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_195_, v___f_193_, v___x_195_);
lean_dec(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_191_ = stack[0].m_obj;
lean_object* v_n_192_ = stack[1].m_obj;
uint8_t v_res_197_;
v_res_197_ = l_Nat_decidableExistsLE___redArg(v_inst_191_, v_n_192_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object* v_inst_198_, lean_object* v_n_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Nat_decidableExistsLE___redArg(v_inst_198_, v_n_199_);
lean_dec(v_n_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
uint8_t l_Nat_decidableExistsLE(lean_object* v_p_202_, lean_object* v_inst_203_, lean_object* v_n_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = l_Nat_decidableExistsLE___redArg(v_inst_203_, v_n_204_);
return v___x_205_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_203_ = stack[1].m_obj;
lean_object* v_n_204_ = stack[2].m_obj;
uint8_t v_res_206_;
v_res_206_ = l_Nat_decidableExistsLE(lean_box(0), v_inst_203_, v_n_204_);
stack->m_num = v_res_206_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object* v_p_207_, lean_object* v_inst_208_, lean_object* v_n_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Nat_decidableExistsLE(v_p_207_, v_inst_208_, v_n_209_);
lean_dec(v_n_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object* v_k_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___f_214_; uint8_t v___x_215_; 
v___f_214_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_214_, 0, v_inst_213_);
lean_inc(v_k_212_);
v___x_215_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_k_212_, v___f_214_, v_k_212_);
lean_dec(v_k_212_);
return v___x_215_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLT_x27TR___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_212_ = stack[0].m_obj;
lean_object* v_inst_213_ = stack[1].m_obj;
uint8_t v_res_216_;
v_res_216_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_212_, v_inst_213_);
stack->m_num = v_res_216_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object* v_k_217_, lean_object* v_inst_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_217_, v_inst_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
uint8_t l_Nat_decidableExistsLT_x27TR(lean_object* v_k_221_, lean_object* v_p_222_, lean_object* v_inst_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_221_, v_inst_223_);
return v___x_224_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLT_x27TR_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_221_ = stack[0].m_obj;
lean_object* v_inst_223_ = stack[2].m_obj;
uint8_t v_res_225_;
v_res_225_ = l_Nat_decidableExistsLT_x27TR(v_k_221_, lean_box(0), v_inst_223_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object* v_k_226_, lean_object* v_p_227_, lean_object* v_inst_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Nat_decidableExistsLT_x27TR(v_k_226_, v_p_227_, v_inst_228_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object* v_I_231_, lean_object* v_i_232_, lean_object* v_h_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_apply_2(v_I_231_, v_i_232_, lean_box(0));
v___x_235_ = lean_unbox(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLE_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_I_231_ = stack[0].m_obj;
lean_object* v_i_232_ = stack[1].m_obj;
uint8_t v_res_236_;
v_res_236_ = l_Nat_decidableExistsLE_x27___redArg___lam__0(v_I_231_, v_i_232_, lean_box(0));
stack->m_num = v_res_236_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object* v_I_237_, lean_object* v_i_238_, lean_object* v_h_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Nat_decidableExistsLE_x27___redArg___lam__0(v_I_237_, v_i_238_, v_h_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object* v_k_242_, lean_object* v_I_243_){
_start:
{
lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___f_244_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_244_, 0, v_I_243_);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_k_242_, v___x_245_);
lean_inc(v___x_246_);
v___x_247_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_246_, v___f_244_, v___x_246_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLE_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_242_ = stack[0].m_obj;
lean_object* v_I_243_ = stack[1].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_Nat_decidableExistsLE_x27___redArg(v_k_242_, v_I_243_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object* v_k_249_, lean_object* v_I_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Nat_decidableExistsLE_x27___redArg(v_k_249_, v_I_250_);
lean_dec(v_k_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_Nat_decidableExistsLE_x27(lean_object* v_k_253_, lean_object* v_p_254_, lean_object* v_I_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = l_Nat_decidableExistsLE_x27___redArg(v_k_253_, v_I_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsLE_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_253_ = stack[0].m_obj;
lean_object* v_I_255_ = stack[2].m_obj;
uint8_t v_res_257_;
v_res_257_ = l_Nat_decidableExistsLE_x27(v_k_253_, lean_box(0), v_I_255_);
stack->m_num = v_res_257_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object* v_k_258_, lean_object* v_p_259_, lean_object* v_I_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Nat_decidableExistsLE_x27(v_k_258_, v_p_259_, v_I_260_);
lean_dec(v_k_258_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object* v_n_263_, lean_object* v_inst_264_, lean_object* v_i_265_, lean_object* v_x_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_nat_dec_lt(v_i_265_, v_n_263_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
lean_dec(v_i_265_);
lean_dec_ref(v_inst_264_);
v___x_268_ = 1;
return v___x_268_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_apply_1(v_inst_264_, v_i_265_);
v___x_270_ = lean_unbox(v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT void l_Nat_decidableExistsFin___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_263_ = stack[0].m_obj;
lean_object* v_inst_264_ = stack[1].m_obj;
lean_object* v_i_265_ = stack[2].m_obj;
uint8_t v_res_271_;
v_res_271_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_263_, v_inst_264_, v_i_265_, lean_box(0));
stack->m_num = v_res_271_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object* v_n_272_, lean_object* v_inst_273_, lean_object* v_i_274_, lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_272_, v_inst_273_, v_i_274_, v_x_275_);
lean_dec(v_n_272_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
uint8_t l_Nat_decidableExistsFin___redArg(lean_object* v_n_278_, lean_object* v_inst_279_){
_start:
{
lean_object* v___f_280_; uint8_t v___x_281_; 
lean_inc_n(v_n_278_, 2);
v___f_280_ = lean_alloc_closure((void*)(l_Nat_decidableExistsFin___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_280_, 0, v_n_278_);
lean_closure_set(v___f_280_, 1, v_inst_279_);
v___x_281_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_278_, v___f_280_, v_n_278_);
lean_dec(v_n_278_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_278_ = stack[0].m_obj;
lean_object* v_inst_279_ = stack[1].m_obj;
uint8_t v_res_282_;
v_res_282_ = l_Nat_decidableExistsFin___redArg(v_n_278_, v_inst_279_);
stack->m_num = v_res_282_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object* v_n_283_, lean_object* v_inst_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Nat_decidableExistsFin___redArg(v_n_283_, v_inst_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
uint8_t l_Nat_decidableExistsFin(lean_object* v_n_287_, lean_object* v_P_288_, lean_object* v_inst_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Nat_decidableExistsFin___redArg(v_n_287_, v_inst_289_);
return v___x_290_;
}
}
LEAN_EXPORT void l_Nat_decidableExistsFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_287_ = stack[0].m_obj;
lean_object* v_inst_289_ = stack[2].m_obj;
uint8_t v_res_291_;
v_res_291_ = l_Nat_decidableExistsFin(v_n_287_, lean_box(0), v_inst_289_);
stack->m_num = v_res_291_;
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object* v_n_292_, lean_object* v_P_293_, lean_object* v_inst_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Nat_decidableExistsFin(v_n_292_, v_P_293_, v_inst_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
