// Lean compiler output
// Module: Init.Data.BitVec.Decidable
// Imports: import Init.Ext public import Init.Data.BitVec.Basic public import Init.PropLemmas import Init.Classical import Init.Data.BitVec.Bootstrap
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_instDecidableForallBitVec___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_instDecidableForallBitVec___redArg___closed__0;
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_BitVec_instDecidableForallBitVecZero___redArg(uint8_t v_x_1_){
_start:
{
return v_x_1_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVecZero___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
uint8_t v_res_2_;
v_res_2_ = l_BitVec_instDecidableForallBitVecZero___redArg(v_x_1_);
stack->m_num = v_res_2_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___redArg___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_x_25__boxed_4_; uint8_t v_res_5_; lean_object* v_r_6_; 
v_x_25__boxed_4_ = lean_unbox(v_x_3_);
v_res_5_ = l_BitVec_instDecidableForallBitVecZero___redArg(v_x_25__boxed_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
uint8_t l_BitVec_instDecidableForallBitVecZero(lean_object* v_P_7_, uint8_t v_x_8_){
_start:
{
return v_x_8_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVecZero_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_8_ = stack[1].m_num;
uint8_t v_res_9_;
v_res_9_ = l_BitVec_instDecidableForallBitVecZero(lean_box(0), v_x_8_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___boxed(lean_object* v_P_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_x_30__boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_x_30__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_BitVec_instDecidableForallBitVecZero(v_P_10_, v_x_30__boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_BitVec_instDecidableForallBitVecSucc___redArg(uint8_t v_inst_15_){
_start:
{
return v_inst_15_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVecSucc___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_15_ = stack[0].m_num;
uint8_t v_res_16_;
v_res_16_ = l_BitVec_instDecidableForallBitVecSucc___redArg(v_inst_15_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(lean_object* v_inst_17_){
_start:
{
uint8_t v_inst_10__boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_inst_10__boxed_18_ = lean_unbox(v_inst_17_);
v_res_19_ = l_BitVec_instDecidableForallBitVecSucc___redArg(v_inst_10__boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_BitVec_instDecidableForallBitVecSucc(lean_object* v_n_21_, lean_object* v_P_22_, lean_object* v_inst_23_, uint8_t v_inst_24_){
_start:
{
return v_inst_24_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVecSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_21_ = stack[0].m_obj;
lean_object* v_inst_23_ = stack[2].m_obj;
uint8_t v_inst_24_ = stack[3].m_num;
uint8_t v_res_25_;
v_res_25_ = l_BitVec_instDecidableForallBitVecSucc(v_n_21_, lean_box(0), v_inst_23_, v_inst_24_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___boxed(lean_object* v_n_26_, lean_object* v_P_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
uint8_t v_inst_16__boxed_30_; uint8_t v_res_31_; lean_object* v_r_32_; 
v_inst_16__boxed_30_ = lean_unbox(v_inst_29_);
v_res_31_ = l_BitVec_instDecidableForallBitVecSucc(v_n_26_, v_P_27_, v_inst_28_, v_inst_16__boxed_30_);
lean_dec_ref(v_inst_28_);
lean_dec(v_n_26_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVecZero___redArg(uint8_t v_inst_33_){
_start:
{
return v_inst_33_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVecZero___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_33_ = stack[0].m_num;
uint8_t v_res_34_;
v_res_34_ = l_BitVec_instDecidableExistsBitVecZero___redArg(v_inst_33_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(lean_object* v_inst_35_){
_start:
{
uint8_t v_inst_47__boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_inst_47__boxed_36_ = lean_unbox(v_inst_35_);
v_res_37_ = l_BitVec_instDecidableExistsBitVecZero___redArg(v_inst_47__boxed_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVecZero(lean_object* v_P_39_, uint8_t v_inst_40_){
_start:
{
return v_inst_40_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVecZero_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_40_ = stack[1].m_num;
uint8_t v_res_41_;
v_res_41_ = l_BitVec_instDecidableExistsBitVecZero(lean_box(0), v_inst_40_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___boxed(lean_object* v_P_42_, lean_object* v_inst_43_){
_start:
{
uint8_t v_inst_52__boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_inst_52__boxed_44_ = lean_unbox(v_inst_43_);
v_res_45_ = l_BitVec_instDecidableExistsBitVecZero(v_P_42_, v_inst_52__boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVecSucc___redArg(uint8_t v_inst_47_){
_start:
{
if (v_inst_47_ == 0)
{
uint8_t v___x_48_; 
v___x_48_ = 1;
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVecSucc___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_47_ = stack[0].m_num;
uint8_t v_res_50_;
v_res_50_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_47_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___redArg___boxed(lean_object* v_inst_51_){
_start:
{
uint8_t v_inst_41__boxed_52_; uint8_t v_res_53_; lean_object* v_r_54_; 
v_inst_41__boxed_52_ = lean_unbox(v_inst_51_);
v_res_53_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_41__boxed_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVecSucc(lean_object* v_n_55_, lean_object* v_P_56_, lean_object* v_inst_57_, uint8_t v_inst_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVecSucc_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_55_ = stack[0].m_obj;
lean_object* v_inst_57_ = stack[2].m_obj;
uint8_t v_inst_58_ = stack[3].m_num;
uint8_t v_res_60_;
v_res_60_ = l_BitVec_instDecidableExistsBitVecSucc(v_n_55_, lean_box(0), v_inst_57_, v_inst_58_);
stack->m_num = v_res_60_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___boxed(lean_object* v_n_61_, lean_object* v_P_62_, lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
uint8_t v_inst_53__boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_inst_53__boxed_65_ = lean_unbox(v_inst_64_);
v_res_66_ = l_BitVec_instDecidableExistsBitVecSucc(v_n_61_, v_P_62_, v_inst_63_, v_inst_53__boxed_65_);
lean_dec_ref(v_inst_63_);
lean_dec(v_n_61_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__0(lean_object* v_n_68_, uint8_t v_a_69_, lean_object* v_x_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = l_BitVec_cons(v_n_68_, v_a_69_, v_a_71_);
v___x_73_ = lean_apply_1(v_x_70_, v___x_72_);
v___x_74_ = lean_unbox(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVec___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_68_ = stack[0].m_obj;
uint8_t v_a_69_ = stack[1].m_num;
lean_object* v_x_70_ = stack[2].m_obj;
lean_object* v_a_71_ = stack[3].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_BitVec_instDecidableForallBitVec___redArg___lam__0(v_n_68_, v_a_69_, v_x_70_, v_a_71_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(lean_object* v_n_76_, lean_object* v_a_77_, lean_object* v_x_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_a_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_a_boxed_80_ = lean_unbox(v_a_77_);
v_res_81_ = l_BitVec_instDecidableForallBitVec___redArg___lam__0(v_n_76_, v_a_boxed_80_, v_x_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec(v_n_76_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
static lean_object* _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0(void){
_start:
{
lean_object* v_zero_83_; lean_object* v___x_84_; 
v_zero_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_BitVec_ofNat(v_zero_83_, v_zero_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(lean_object* v_n_85_, lean_object* v_x_86_, lean_object* v_a_87_){
_start:
{
uint8_t v_a_boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_a_boxed_88_ = lean_unbox(v_a_87_);
v_res_89_ = l_BitVec_instDecidableForallBitVec___redArg___lam__1(v_n_85_, v_x_86_, v_a_boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_zero_93_; uint8_t v_isZero_94_; 
v_zero_93_ = lean_unsigned_to_nat(0u);
v_isZero_94_ = lean_nat_dec_eq(v_x_91_, v_zero_93_);
if (v_isZero_94_ == 1)
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = lean_obj_once(&l_BitVec_instDecidableForallBitVec___redArg___closed__0, &l_BitVec_instDecidableForallBitVec___redArg___closed__0_once, _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0);
v___x_96_ = lean_apply_1(v_x_92_, v___x_95_);
v___x_97_ = lean_unbox(v___x_96_);
return v___x_97_;
}
else
{
lean_object* v_one_98_; lean_object* v_n_99_; lean_object* v___f_100_; uint8_t v___x_101_; 
v_one_98_ = lean_unsigned_to_nat(1u);
v_n_99_ = lean_nat_sub(v_x_91_, v_one_98_);
v___f_100_ = lean_alloc_closure((void*)(l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_100_, 0, v_n_99_);
lean_closure_set(v___f_100_, 1, v_x_92_);
v___x_101_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_91_ = stack[0].m_obj;
lean_object* v_x_92_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_91_, v_x_92_);
stack->m_num = v_res_102_;
}
uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__1(lean_object* v_n_103_, lean_object* v_x_104_, uint8_t v_a_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___f_107_; uint8_t v___x_108_; 
v___x_106_ = lean_box(v_a_105_);
lean_inc(v_n_103_);
v___f_107_ = lean_alloc_closure((void*)(l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_107_, 0, v_n_103_);
lean_closure_set(v___f_107_, 1, v___x_106_);
lean_closure_set(v___f_107_, 2, v_x_104_);
v___x_108_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_103_, v___f_107_);
lean_dec(v_n_103_);
return v___x_108_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVec___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
uint8_t v_a_105_ = stack[2].m_num;
uint8_t v_res_109_;
v_res_109_ = l_BitVec_instDecidableForallBitVec___redArg___lam__1(v_n_103_, v_x_104_, v_a_105_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_110_, v_x_111_);
lean_dec(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_BitVec_instDecidableForallBitVec(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_114_, v_x_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableForallBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_114_ = stack[0].m_obj;
lean_object* v_x_116_ = stack[2].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_BitVec_instDecidableForallBitVec(v_x_114_, lean_box(0), v_x_116_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___boxed(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_BitVec_instDecidableForallBitVec(v_x_119_, v_x_120_, v_x_121_);
lean_dec(v_x_119_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__0(lean_object* v_n_124_, uint8_t v_a_125_, lean_object* v_x_126_, uint8_t v_isZero_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_BitVec_cons(v_n_124_, v_a_125_, v_a_128_);
v___x_130_ = lean_apply_1(v_x_126_, v___x_129_);
v___x_131_ = lean_unbox(v___x_130_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
else
{
return v_isZero_127_;
}
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVec___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_124_ = stack[0].m_obj;
uint8_t v_a_125_ = stack[1].m_num;
lean_object* v_x_126_ = stack[2].m_obj;
uint8_t v_isZero_127_ = stack[3].m_num;
lean_object* v_a_128_ = stack[4].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__0(v_n_124_, v_a_125_, v_x_126_, v_isZero_127_, v_a_128_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(lean_object* v_n_134_, lean_object* v_a_135_, lean_object* v_x_136_, lean_object* v_isZero_137_, lean_object* v_a_138_){
_start:
{
uint8_t v_a_boxed_139_; uint8_t v_isZero_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_a_boxed_139_ = lean_unbox(v_a_135_);
v_isZero_boxed_140_ = lean_unbox(v_isZero_137_);
v_res_141_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__0(v_n_134_, v_a_boxed_139_, v_x_136_, v_isZero_boxed_140_, v_a_138_);
lean_dec(v_a_138_);
lean_dec(v_n_134_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__1(lean_object* v_n_143_, lean_object* v_x_144_, uint8_t v_isZero_145_, uint8_t v_a_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___f_149_; uint8_t v___x_150_; 
v___x_147_ = lean_box(v_a_146_);
v___x_148_ = lean_box(v_isZero_145_);
lean_inc(v_n_143_);
v___f_149_ = lean_alloc_closure((void*)(l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_149_, 0, v_n_143_);
lean_closure_set(v___f_149_, 1, v___x_147_);
lean_closure_set(v___f_149_, 2, v_x_144_);
lean_closure_set(v___f_149_, 3, v___x_148_);
v___x_150_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_143_, v___f_149_);
lean_dec(v_n_143_);
return v___x_150_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVec___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_143_ = stack[0].m_obj;
lean_object* v_x_144_ = stack[1].m_obj;
uint8_t v_isZero_145_ = stack[2].m_num;
uint8_t v_a_146_ = stack[3].m_num;
uint8_t v_res_151_;
v_res_151_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__1(v_n_143_, v_x_144_, v_isZero_145_, v_a_146_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(lean_object* v_n_152_, lean_object* v_x_153_, lean_object* v_isZero_154_, lean_object* v_a_155_){
_start:
{
uint8_t v_isZero_boxed_156_; uint8_t v_a_boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_isZero_boxed_156_ = lean_unbox(v_isZero_154_);
v_a_boxed_157_ = lean_unbox(v_a_155_);
v_res_158_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__1(v_n_152_, v_x_153_, v_isZero_boxed_156_, v_a_boxed_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_zero_162_; uint8_t v_isZero_163_; 
v_zero_162_ = lean_unsigned_to_nat(0u);
v_isZero_163_ = lean_nat_dec_eq(v_x_160_, v_zero_162_);
if (v_isZero_163_ == 1)
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_164_ = lean_obj_once(&l_BitVec_instDecidableForallBitVec___redArg___closed__0, &l_BitVec_instDecidableForallBitVec___redArg___closed__0_once, _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0);
v___x_165_ = lean_apply_1(v_x_161_, v___x_164_);
v___x_166_ = lean_unbox(v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_one_167_; lean_object* v_n_168_; lean_object* v___x_169_; lean_object* v___f_170_; uint8_t v___x_171_; uint8_t v___x_172_; 
v_one_167_ = lean_unsigned_to_nat(1u);
v_n_168_ = lean_nat_sub(v_x_160_, v_one_167_);
v___x_169_ = lean_box(v_isZero_163_);
v___f_170_ = lean_alloc_closure((void*)(l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_170_, 0, v_n_168_);
lean_closure_set(v___f_170_, 1, v_x_161_);
lean_closure_set(v___f_170_, 2, v___x_169_);
v___x_171_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_170_);
v___x_172_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v___x_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_160_ = stack[0].m_obj;
lean_object* v_x_161_ = stack[1].m_obj;
uint8_t v_res_173_;
v_res_173_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_160_, v_x_161_);
stack->m_num = v_res_173_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___boxed(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_174_, v_x_175_);
lean_dec(v_x_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
uint8_t l_BitVec_instDecidableExistsBitVec(lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_178_, v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT void l_BitVec_instDecidableExistsBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_178_ = stack[0].m_obj;
lean_object* v_x_180_ = stack[2].m_obj;
uint8_t v_res_182_;
v_res_182_ = l_BitVec_instDecidableExistsBitVec(v_x_178_, lean_box(0), v_x_180_);
stack->m_num = v_res_182_;
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___boxed(lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_BitVec_instDecidableExistsBitVec(v_x_183_, v_x_184_, v_x_185_);
lean_dec(v_x_183_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Decidable(builtin);
}
#ifdef __cplusplus
}
#endif
