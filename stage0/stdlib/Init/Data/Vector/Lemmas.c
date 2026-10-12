// Lean compiler output
// Module: Init.Data.Vector.Lemmas
// Imports: import all Init.Data.Array.Basic public import Init.Data.Vector.Basic import all Init.Data.Vector.Basic public import Init.Data.List.MapIdx import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.Count import Init.Data.Array.Find import Init.Data.Array.OfFn import Init.Data.Bool import Init.Data.Fin.Lemmas import Init.Data.List.TakeDrop import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableMemOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorZero(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableForallVectorSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorZero(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Vector_instDecidableExistsVectorSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(lean_object* v_xs_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_array_fget_borrowed(v_xs_1_, v_i_3_);
lean_inc(v___x_5_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_i_3_ = stack[2].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_1_, v_inst_2_, v_i_3_, lean_box(0));
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(lean_object* v_xs_9_, lean_object* v_inst_10_, lean_object* v_i_11_, lean_object* v_h_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(v_xs_9_, v_inst_10_, v_i_11_, v_h_12_);
lean_dec(v_i_11_);
lean_dec_ref(v_xs_9_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(lean_object* v_n_15_, lean_object* v_xs_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_18_, 0, v_xs_16_);
lean_closure_set(v___f_18_, 1, v_inst_17_);
lean_inc(v_n_15_);
v___x_19_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v_n_15_, v___f_18_, v_n_15_, lean_box(0));
lean_dec(v_n_15_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallForallMemOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_15_ = stack[0].m_obj;
lean_object* v_xs_16_ = stack[1].m_obj;
lean_object* v_inst_17_ = stack[2].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_15_, v_xs_16_, v_inst_17_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___boxed(lean_object* v_n_21_, lean_object* v_xs_22_, lean_object* v_inst_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_21_, v_xs_22_, v_inst_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_Vector_instDecidableForallForallMemOfDecidablePred(lean_object* v_00_u03b1_26_, lean_object* v_n_27_, lean_object* v_xs_28_, lean_object* v_p_29_, lean_object* v_inst_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = l_Vector_instDecidableForallForallMemOfDecidablePred___redArg(v_n_27_, v_xs_28_, v_inst_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallForallMemOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_27_ = stack[1].m_obj;
lean_object* v_xs_28_ = stack[2].m_obj;
lean_object* v_inst_30_ = stack[4].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Vector_instDecidableForallForallMemOfDecidablePred(lean_box(0), v_n_27_, v_xs_28_, lean_box(0), v_inst_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallForallMemOfDecidablePred___boxed(lean_object* v_00_u03b1_33_, lean_object* v_n_34_, lean_object* v_xs_35_, lean_object* v_p_36_, lean_object* v_inst_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Vector_instDecidableForallForallMemOfDecidablePred(v_00_u03b1_33_, v_n_34_, v_xs_35_, v_p_36_, v_inst_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(lean_object* v_n_40_, lean_object* v_xs_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v___f_43_; uint8_t v___x_44_; 
v___f_43_ = lean_alloc_closure((void*)(l_Vector_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_43_, 0, v_xs_41_);
lean_closure_set(v___f_43_, 1, v_inst_42_);
lean_inc(v_n_40_);
v___x_44_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_40_, v___f_43_, v_n_40_, lean_box(0));
lean_dec(v_n_40_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_40_ = stack[0].m_obj;
lean_object* v_xs_41_ = stack[1].m_obj;
lean_object* v_inst_42_ = stack[2].m_obj;
uint8_t v_res_45_;
v_res_45_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_40_, v_xs_41_, v_inst_42_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(lean_object* v_n_46_, lean_object* v_xs_47_, lean_object* v_inst_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_46_, v_xs_47_, v_inst_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
uint8_t l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_object* v_00_u03b1_51_, lean_object* v_n_52_, lean_object* v_xs_53_, lean_object* v_p_54_, lean_object* v_inst_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = l_Vector_instDecidableExistsAndMemOfDecidablePred___redArg(v_n_52_, v_xs_53_, v_inst_55_);
return v___x_56_;
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsAndMemOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_52_ = stack[1].m_obj;
lean_object* v_xs_53_ = stack[2].m_obj;
lean_object* v_inst_55_ = stack[4].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Vector_instDecidableExistsAndMemOfDecidablePred(lean_box(0), v_n_52_, v_xs_53_, lean_box(0), v_inst_55_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsAndMemOfDecidablePred___boxed(lean_object* v_00_u03b1_58_, lean_object* v_n_59_, lean_object* v_xs_60_, lean_object* v_p_61_, lean_object* v_inst_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Vector_instDecidableExistsAndMemOfDecidablePred(v_00_u03b1_58_, v_n_59_, v_xs_60_, v_p_61_, v_inst_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l_Vector_instDecidableMemOfLawfulBEq___redArg(lean_object* v_inst_65_, lean_object* v_a_66_, lean_object* v_as_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l_Array_contains___redArg(v_inst_65_, v_as_67_, v_a_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Vector_instDecidableMemOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_65_ = stack[0].m_obj;
lean_object* v_a_66_ = stack[1].m_obj;
lean_object* v_as_67_ = stack[2].m_obj;
uint8_t v_res_69_;
v_res_69_ = l_Vector_instDecidableMemOfLawfulBEq___redArg(v_inst_65_, v_a_66_, v_as_67_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___redArg___boxed(lean_object* v_inst_70_, lean_object* v_a_71_, lean_object* v_as_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Vector_instDecidableMemOfLawfulBEq___redArg(v_inst_70_, v_a_71_, v_as_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Vector_instDecidableMemOfLawfulBEq(lean_object* v_00_u03b1_75_, lean_object* v_n_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_a_79_, lean_object* v_as_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_Array_contains___redArg(v_inst_77_, v_as_80_, v_a_79_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Vector_instDecidableMemOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_76_ = stack[1].m_obj;
lean_object* v_inst_77_ = stack[2].m_obj;
lean_object* v_a_79_ = stack[4].m_obj;
lean_object* v_as_80_ = stack[5].m_obj;
uint8_t v_res_82_;
v_res_82_ = l_Vector_instDecidableMemOfLawfulBEq(lean_box(0), v_n_76_, v_inst_77_, lean_box(0), v_a_79_, v_as_80_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableMemOfLawfulBEq___boxed(lean_object* v_00_u03b1_83_, lean_object* v_n_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_a_87_, lean_object* v_as_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Vector_instDecidableMemOfLawfulBEq(v_00_u03b1_83_, v_n_84_, v_inst_85_, v_inst_86_, v_a_87_, v_as_88_);
lean_dec(v_n_84_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_Vector_instDecidableForallVectorZero___redArg(uint8_t v_x_91_){
_start:
{
return v_x_91_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallVectorZero___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_91_ = stack[0].m_num;
uint8_t v_res_92_;
v_res_92_ = l_Vector_instDecidableForallVectorZero___redArg(v_x_91_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___redArg___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_25__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_x_25__boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l_Vector_instDecidableForallVectorZero___redArg(v_x_25__boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
uint8_t l_Vector_instDecidableForallVectorZero(lean_object* v_00_u03b1_97_, lean_object* v_P_98_, uint8_t v_x_99_){
_start:
{
return v_x_99_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallVectorZero_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_99_ = stack[2].m_num;
uint8_t v_res_100_;
v_res_100_ = l_Vector_instDecidableForallVectorZero(lean_box(0), lean_box(0), v_x_99_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorZero___boxed(lean_object* v_00_u03b1_101_, lean_object* v_P_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_x_30__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_x_30__boxed_104_ = lean_unbox(v_x_103_);
v_res_105_ = l_Vector_instDecidableForallVectorZero(v_00_u03b1_101_, v_P_102_, v_x_30__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
uint8_t l_Vector_instDecidableForallVectorSucc___redArg(uint8_t v_inst_107_){
_start:
{
return v_inst_107_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallVectorSucc___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_107_ = stack[0].m_num;
uint8_t v_res_108_;
v_res_108_ = l_Vector_instDecidableForallVectorSucc___redArg(v_inst_107_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___redArg___boxed(lean_object* v_inst_109_){
_start:
{
uint8_t v_inst_8__boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_inst_8__boxed_110_ = lean_unbox(v_inst_109_);
v_res_111_ = l_Vector_instDecidableForallVectorSucc___redArg(v_inst_8__boxed_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l_Vector_instDecidableForallVectorSucc(lean_object* v_00_u03b1_113_, lean_object* v_n_114_, lean_object* v_P_115_, uint8_t v_inst_116_){
_start:
{
return v_inst_116_;
}
}
LEAN_EXPORT void l_Vector_instDecidableForallVectorSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_114_ = stack[1].m_obj;
uint8_t v_inst_116_ = stack[3].m_num;
uint8_t v_res_117_;
v_res_117_ = l_Vector_instDecidableForallVectorSucc(lean_box(0), v_n_114_, lean_box(0), v_inst_116_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableForallVectorSucc___boxed(lean_object* v_00_u03b1_118_, lean_object* v_n_119_, lean_object* v_P_120_, lean_object* v_inst_121_){
_start:
{
uint8_t v_inst_13__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_inst_13__boxed_122_ = lean_unbox(v_inst_121_);
v_res_123_ = l_Vector_instDecidableForallVectorSucc(v_00_u03b1_118_, v_n_119_, v_P_120_, v_inst_13__boxed_122_);
lean_dec(v_n_119_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
uint8_t l_Vector_instDecidableExistsVectorZero___redArg(uint8_t v_inst_125_){
_start:
{
return v_inst_125_;
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsVectorZero___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_125_ = stack[0].m_num;
uint8_t v_res_126_;
v_res_126_ = l_Vector_instDecidableExistsVectorZero___redArg(v_inst_125_);
stack->m_num = v_res_126_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___redArg___boxed(lean_object* v_inst_127_){
_start:
{
uint8_t v_inst_47__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_inst_47__boxed_128_ = lean_unbox(v_inst_127_);
v_res_129_ = l_Vector_instDecidableExistsVectorZero___redArg(v_inst_47__boxed_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
uint8_t l_Vector_instDecidableExistsVectorZero(lean_object* v_00_u03b1_131_, lean_object* v_P_132_, uint8_t v_inst_133_){
_start:
{
return v_inst_133_;
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsVectorZero_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_133_ = stack[2].m_num;
uint8_t v_res_134_;
v_res_134_ = l_Vector_instDecidableExistsVectorZero(lean_box(0), lean_box(0), v_inst_133_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorZero___boxed(lean_object* v_00_u03b1_135_, lean_object* v_P_136_, lean_object* v_inst_137_){
_start:
{
uint8_t v_inst_52__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_inst_52__boxed_138_ = lean_unbox(v_inst_137_);
v_res_139_ = l_Vector_instDecidableExistsVectorZero(v_00_u03b1_135_, v_P_136_, v_inst_52__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
uint8_t l_Vector_instDecidableExistsVectorSucc___redArg(uint8_t v_inst_141_){
_start:
{
if (v_inst_141_ == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 1;
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsVectorSucc___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_141_ = stack[0].m_num;
uint8_t v_res_144_;
v_res_144_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_141_);
stack->m_num = v_res_144_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___redArg___boxed(lean_object* v_inst_145_){
_start:
{
uint8_t v_inst_34__boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_inst_34__boxed_146_ = lean_unbox(v_inst_145_);
v_res_147_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_34__boxed_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
uint8_t l_Vector_instDecidableExistsVectorSucc(lean_object* v_00_u03b1_149_, lean_object* v_n_150_, lean_object* v_P_151_, uint8_t v_inst_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_Vector_instDecidableExistsVectorSucc___redArg(v_inst_152_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Vector_instDecidableExistsVectorSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_150_ = stack[1].m_obj;
uint8_t v_inst_152_ = stack[3].m_num;
uint8_t v_res_154_;
v_res_154_ = l_Vector_instDecidableExistsVectorSucc(lean_box(0), v_n_150_, lean_box(0), v_inst_152_);
stack->m_num = v_res_154_;
}
LEAN_EXPORT lean_object* l_Vector_instDecidableExistsVectorSucc___boxed(lean_object* v_00_u03b1_155_, lean_object* v_n_156_, lean_object* v_P_157_, lean_object* v_inst_158_){
_start:
{
uint8_t v_inst_45__boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_inst_45__boxed_159_ = lean_unbox(v_inst_158_);
v_res_160_ = l_Vector_instDecidableExistsVectorSucc(v_00_u03b1_155_, v_n_156_, v_P_157_, v_inst_45__boxed_159_);
lean_dec(v_n_156_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Find(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
