// Lean compiler output
// Module: Init.Data.Int.DivMod.Basic
// Imports: public import Init.Data.Int.Basic import Init.Data.Nat.Div.Basic
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ediv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instDiv___closed__0 = (const lean_object*)&l_Int_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instDiv = (const lean_object*)&l_Int_instDiv___closed__0_value;
static const lean_closure_object l_Int_instMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_emod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instMod___closed__0 = (const lean_object*)&l_Int_instMod___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instMod = (const lean_object*)&l_Int_instMod___closed__0_value;
lean_object* lean_int_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int_fdiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_fdiv___closed__0;
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_bmod_spec__0(lean_object*);
static lean_once_cell_t l_Int_bmod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_bmod___closed__0;
static lean_once_cell_t l_Int_bmod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_bmod___closed__1;
LEAN_EXPORT lean_object* l_Int_bmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT void l_Int_ediv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_2_ = stack[1].m_obj;
lean_object* v_res_3_;
v_res_3_ = lean_int_ediv(v_a_00___x40___internal___hyg_1_, v_a_00___x40___internal___hyg_2_);
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object* v_a_00___x40___internal___hyg_4_, lean_object* v_a_00___x40___internal___hyg_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_int_ediv(v_a_00___x40___internal___hyg_4_, v_a_00___x40___internal___hyg_5_);
lean_dec(v_a_00___x40___internal___hyg_5_);
lean_dec(v_a_00___x40___internal___hyg_4_);
return v_res_6_;
}
}
LEAN_EXPORT void l_Int_emod_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_7_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_8_ = stack[1].m_obj;
lean_object* v_res_9_;
v_res_9_ = lean_int_emod(v_a_00___x40___internal___hyg_7_, v_a_00___x40___internal___hyg_8_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object* v_a_00___x40___internal___hyg_10_, lean_object* v_a_00___x40___internal___hyg_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lean_int_emod(v_a_00___x40___internal___hyg_10_, v_a_00___x40___internal___hyg_11_);
lean_dec(v_a_00___x40___internal___hyg_11_);
lean_dec(v_a_00___x40___internal___hyg_10_);
return v_res_12_;
}
}
LEAN_EXPORT void l_Int_divExact_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_17_ = stack[0].m_obj;
lean_object* v_y_18_ = stack[1].m_obj;
lean_object* v_res_20_;
v_res_20_ = lean_int_div_exact(v_x_17_, v_y_18_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object* v_x_21_, lean_object* v_y_22_, lean_object* v_h_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lean_int_div_exact(v_x_21_, v_y_22_);
lean_dec(v_y_22_);
lean_dec(v_x_21_);
return v_res_24_;
}
}
LEAN_EXPORT void l_Int_tdiv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_25_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_26_ = stack[1].m_obj;
lean_object* v_res_27_;
v_res_27_ = lean_int_div(v_a_00___x40___internal___hyg_25_, v_a_00___x40___internal___hyg_26_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object* v_a_00___x40___internal___hyg_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_int_div(v_a_00___x40___internal___hyg_28_, v_a_00___x40___internal___hyg_29_);
lean_dec(v_a_00___x40___internal___hyg_29_);
lean_dec(v_a_00___x40___internal___hyg_28_);
return v_res_30_;
}
}
LEAN_EXPORT void l_Int_tmod_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_31_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_32_ = stack[1].m_obj;
lean_object* v_res_33_;
v_res_33_ = lean_int_mod(v_a_00___x40___internal___hyg_31_, v_a_00___x40___internal___hyg_32_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object* v_a_00___x40___internal___hyg_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_int_mod(v_a_00___x40___internal___hyg_34_, v_a_00___x40___internal___hyg_35_);
lean_dec(v_a_00___x40___internal___hyg_35_);
lean_dec(v_a_00___x40___internal___hyg_34_);
return v_res_36_;
}
}
static lean_object* _init_l_Int_fdiv___closed__0(void){
_start:
{
lean_object* v_natZero_37_; lean_object* v_intZero_38_; 
v_natZero_37_ = lean_unsigned_to_nat(0u);
v_intZero_38_ = lean_nat_to_int(v_natZero_37_);
return v_intZero_38_;
}
}
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_m_42_; lean_object* v_n_43_; lean_object* v_natZero_48_; lean_object* v_intZero_49_; uint8_t v_isNeg_50_; 
v_natZero_48_ = lean_unsigned_to_nat(0u);
v_intZero_49_ = lean_obj_once(&l_Int_fdiv___closed__0, &l_Int_fdiv___closed__0_once, _init_l_Int_fdiv___closed__0);
v_isNeg_50_ = lean_int_dec_lt(v_x_39_, v_intZero_49_);
if (v_isNeg_50_ == 0)
{
lean_object* v_a_51_; uint8_t v_isZero_52_; 
v_a_51_ = lean_nat_abs(v_x_39_);
v_isZero_52_ = lean_nat_dec_eq(v_a_51_, v_natZero_48_);
if (v_isZero_52_ == 1)
{
lean_dec(v_a_51_);
return v_intZero_49_;
}
else
{
uint8_t v_isNeg_53_; 
v_isNeg_53_ = lean_int_dec_lt(v_x_40_, v_intZero_49_);
if (v_isNeg_53_ == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_a_54_ = lean_nat_abs(v_x_40_);
v___x_55_ = lean_nat_div(v_a_51_, v_a_54_);
lean_dec(v_a_54_);
lean_dec(v_a_51_);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_one_57_; lean_object* v_n_58_; lean_object* v_abs_59_; lean_object* v_a_60_; 
v_one_57_ = lean_unsigned_to_nat(1u);
v_n_58_ = lean_nat_sub(v_a_51_, v_one_57_);
lean_dec(v_a_51_);
v_abs_59_ = lean_nat_abs(v_x_40_);
v_a_60_ = lean_nat_sub(v_abs_59_, v_one_57_);
lean_dec(v_abs_59_);
v_m_42_ = v_n_58_;
v_n_43_ = v_a_60_;
goto v___jp_41_;
}
}
}
else
{
lean_object* v_abs_61_; lean_object* v_one_62_; lean_object* v_a_63_; uint8_t v_isNeg_64_; 
v_abs_61_ = lean_nat_abs(v_x_39_);
v_one_62_ = lean_unsigned_to_nat(1u);
v_a_63_ = lean_nat_sub(v_abs_61_, v_one_62_);
lean_dec(v_abs_61_);
v_isNeg_64_ = lean_int_dec_lt(v_x_40_, v_intZero_49_);
if (v_isNeg_64_ == 0)
{
lean_object* v_a_65_; uint8_t v_isZero_66_; 
v_a_65_ = lean_nat_abs(v_x_40_);
v_isZero_66_ = lean_nat_dec_eq(v_a_65_, v_natZero_48_);
if (v_isZero_66_ == 1)
{
lean_dec(v_a_65_);
lean_dec(v_a_63_);
return v_intZero_49_;
}
else
{
lean_object* v_n_67_; 
v_n_67_ = lean_nat_sub(v_a_65_, v_one_62_);
lean_dec(v_a_65_);
v_m_42_ = v_a_63_;
v_n_43_ = v_n_67_;
goto v___jp_41_;
}
}
else
{
lean_object* v_abs_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_abs_68_ = lean_nat_abs(v_x_40_);
v_a_69_ = lean_nat_sub(v_abs_68_, v_one_62_);
lean_dec(v_abs_68_);
v___x_70_ = lean_nat_add(v_a_63_, v_one_62_);
lean_dec(v_a_63_);
v___x_71_ = lean_nat_add(v_a_69_, v_one_62_);
lean_dec(v_a_69_);
v___x_72_ = lean_nat_div(v___x_70_, v___x_71_);
lean_dec(v___x_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
v___jp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_n_43_, v___x_44_);
lean_dec(v_n_43_);
v___x_46_ = lean_nat_div(v_m_42_, v___x_45_);
lean_dec(v___x_45_);
lean_dec(v_m_42_);
v___x_47_ = lean_int_neg_succ_of_nat(v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Int_fdiv(v_x_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v_x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Int_fmod(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_natZero_79_; lean_object* v_intZero_80_; uint8_t v_isNeg_81_; 
v_natZero_79_ = lean_unsigned_to_nat(0u);
v_intZero_80_ = lean_obj_once(&l_Int_fdiv___closed__0, &l_Int_fdiv___closed__0_once, _init_l_Int_fdiv___closed__0);
v_isNeg_81_ = lean_int_dec_lt(v_x_77_, v_intZero_80_);
if (v_isNeg_81_ == 0)
{
lean_object* v_a_82_; uint8_t v_isZero_83_; 
v_a_82_ = lean_nat_abs(v_x_77_);
v_isZero_83_ = lean_nat_dec_eq(v_a_82_, v_natZero_79_);
if (v_isZero_83_ == 1)
{
lean_dec(v_a_82_);
return v_intZero_80_;
}
else
{
uint8_t v_isNeg_84_; 
v_isNeg_84_ = lean_int_dec_lt(v_x_78_, v_intZero_80_);
if (v_isNeg_84_ == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_a_85_ = lean_nat_abs(v_x_78_);
v___x_86_ = lean_nat_mod(v_a_82_, v_a_85_);
lean_dec(v_a_85_);
lean_dec(v_a_82_);
v___x_87_ = lean_nat_to_int(v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_one_88_; lean_object* v_n_89_; lean_object* v_abs_90_; lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_one_88_ = lean_unsigned_to_nat(1u);
v_n_89_ = lean_nat_sub(v_a_82_, v_one_88_);
lean_dec(v_a_82_);
v_abs_90_ = lean_nat_abs(v_x_78_);
v_a_91_ = lean_nat_sub(v_abs_90_, v_one_88_);
lean_dec(v_abs_90_);
v___x_92_ = lean_nat_add(v_a_91_, v_one_88_);
v___x_93_ = lean_nat_mod(v_n_89_, v___x_92_);
lean_dec(v___x_92_);
lean_dec(v_n_89_);
v___x_94_ = l_Int_subNatNat(v___x_93_, v_a_91_);
lean_dec(v_a_91_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
}
else
{
lean_object* v_abs_95_; lean_object* v_one_96_; lean_object* v_a_97_; uint8_t v_isNeg_98_; 
v_abs_95_ = lean_nat_abs(v_x_77_);
v_one_96_ = lean_unsigned_to_nat(1u);
v_a_97_ = lean_nat_sub(v_abs_95_, v_one_96_);
lean_dec(v_abs_95_);
v_isNeg_98_ = lean_int_dec_lt(v_x_78_, v_intZero_80_);
if (v_isNeg_98_ == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_a_99_ = lean_nat_abs(v_x_78_);
v___x_100_ = lean_nat_mod(v_a_97_, v_a_99_);
lean_dec(v_a_97_);
v___x_101_ = lean_nat_add(v___x_100_, v_one_96_);
lean_dec(v___x_100_);
v___x_102_ = l_Int_subNatNat(v_a_99_, v___x_101_);
lean_dec(v___x_101_);
lean_dec(v_a_99_);
return v___x_102_;
}
else
{
lean_object* v_abs_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_abs_103_ = lean_nat_abs(v_x_78_);
v_a_104_ = lean_nat_sub(v_abs_103_, v_one_96_);
lean_dec(v_abs_103_);
v___x_105_ = lean_nat_add(v_a_97_, v_one_96_);
lean_dec(v_a_97_);
v___x_106_ = lean_nat_add(v_a_104_, v_one_96_);
lean_dec(v_a_104_);
v___x_107_ = lean_nat_mod(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_nat_to_int(v___x_107_);
v___x_109_ = lean_int_neg(v___x_108_);
lean_dec(v___x_108_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Int_fmod(v_x_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec(v_x_110_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_113_; lean_object* v_intZero_114_; 
v_natZero_113_ = lean_unsigned_to_nat(0u);
v_intZero_114_ = lean_nat_to_int(v_natZero_113_);
return v_intZero_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_, lean_object* v_h__3_119_, lean_object* v_h__4_120_, lean_object* v_h__5_121_, lean_object* v_h__6_122_){
_start:
{
lean_object* v_natZero_123_; lean_object* v_intZero_124_; uint8_t v_isNeg_125_; 
v_natZero_123_ = lean_unsigned_to_nat(0u);
v_intZero_124_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_125_ = lean_int_dec_lt(v_x_115_, v_intZero_124_);
if (v_isNeg_125_ == 0)
{
lean_object* v_a_126_; uint8_t v_isZero_127_; 
lean_dec(v_h__6_122_);
lean_dec(v_h__5_121_);
lean_dec(v_h__4_120_);
v_a_126_ = lean_nat_abs(v_x_115_);
v_isZero_127_ = lean_nat_dec_eq(v_a_126_, v_natZero_123_);
if (v_isZero_127_ == 1)
{
lean_object* v___x_128_; 
lean_dec(v_a_126_);
lean_dec(v_h__3_119_);
lean_dec(v_h__2_118_);
v___x_128_ = lean_apply_1(v_h__1_117_, v_x_116_);
return v___x_128_;
}
else
{
uint8_t v_isNeg_129_; 
lean_dec(v_h__1_117_);
v_isNeg_129_ = lean_int_dec_lt(v_x_116_, v_intZero_124_);
if (v_isNeg_129_ == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
lean_dec(v_h__3_119_);
v_a_130_ = lean_nat_abs(v_x_116_);
lean_dec(v_x_116_);
v___x_131_ = lean_apply_3(v_h__2_118_, v_a_126_, v_a_130_, lean_box(0));
return v___x_131_;
}
else
{
lean_object* v_one_132_; lean_object* v_n_133_; lean_object* v_abs_134_; lean_object* v_a_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_118_);
v_one_132_ = lean_unsigned_to_nat(1u);
v_n_133_ = lean_nat_sub(v_a_126_, v_one_132_);
lean_dec(v_a_126_);
v_abs_134_ = lean_nat_abs(v_x_116_);
lean_dec(v_x_116_);
v_a_135_ = lean_nat_sub(v_abs_134_, v_one_132_);
lean_dec(v_abs_134_);
v___x_136_ = lean_apply_2(v_h__3_119_, v_n_133_, v_a_135_);
return v___x_136_;
}
}
}
else
{
lean_object* v_abs_137_; lean_object* v_one_138_; lean_object* v_a_139_; uint8_t v_isNeg_140_; 
lean_dec(v_h__3_119_);
lean_dec(v_h__2_118_);
lean_dec(v_h__1_117_);
v_abs_137_ = lean_nat_abs(v_x_115_);
v_one_138_ = lean_unsigned_to_nat(1u);
v_a_139_ = lean_nat_sub(v_abs_137_, v_one_138_);
lean_dec(v_abs_137_);
v_isNeg_140_ = lean_int_dec_lt(v_x_116_, v_intZero_124_);
if (v_isNeg_140_ == 0)
{
lean_object* v_a_141_; uint8_t v_isZero_142_; 
lean_dec(v_h__6_122_);
v_a_141_ = lean_nat_abs(v_x_116_);
lean_dec(v_x_116_);
v_isZero_142_ = lean_nat_dec_eq(v_a_141_, v_natZero_123_);
if (v_isZero_142_ == 1)
{
lean_object* v___x_143_; 
lean_dec(v_a_141_);
lean_dec(v_h__5_121_);
v___x_143_ = lean_apply_1(v_h__4_120_, v_a_139_);
return v___x_143_;
}
else
{
lean_object* v_n_144_; lean_object* v___x_145_; 
lean_dec(v_h__4_120_);
v_n_144_ = lean_nat_sub(v_a_141_, v_one_138_);
lean_dec(v_a_141_);
v___x_145_ = lean_apply_2(v_h__5_121_, v_a_139_, v_n_144_);
return v___x_145_;
}
}
else
{
lean_object* v_abs_146_; lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__5_121_);
lean_dec(v_h__4_120_);
v_abs_146_ = lean_nat_abs(v_x_116_);
lean_dec(v_x_116_);
v_a_147_ = lean_nat_sub(v_abs_146_, v_one_138_);
lean_dec(v_abs_146_);
v___x_148_ = lean_apply_2(v_h__6_122_, v_a_139_, v_a_147_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_, lean_object* v_h__4_154_, lean_object* v_h__5_155_, lean_object* v_h__6_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(v_x_149_, v_x_150_, v_h__1_151_, v_h__2_152_, v_h__3_153_, v_h__4_154_, v_h__5_155_, v_h__6_156_);
lean_dec(v_x_149_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object* v_motive_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_, lean_object* v_h__4_164_, lean_object* v_h__5_165_, lean_object* v_h__6_166_){
_start:
{
lean_object* v_natZero_167_; lean_object* v_intZero_168_; uint8_t v_isNeg_169_; 
v_natZero_167_ = lean_unsigned_to_nat(0u);
v_intZero_168_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_169_ = lean_int_dec_lt(v_x_159_, v_intZero_168_);
if (v_isNeg_169_ == 0)
{
lean_object* v_a_170_; uint8_t v_isZero_171_; 
lean_dec(v_h__6_166_);
lean_dec(v_h__5_165_);
lean_dec(v_h__4_164_);
v_a_170_ = lean_nat_abs(v_x_159_);
v_isZero_171_ = lean_nat_dec_eq(v_a_170_, v_natZero_167_);
if (v_isZero_171_ == 1)
{
lean_object* v___x_172_; 
lean_dec(v_a_170_);
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
v___x_172_ = lean_apply_1(v_h__1_161_, v_x_160_);
return v___x_172_;
}
else
{
uint8_t v_isNeg_173_; 
lean_dec(v_h__1_161_);
v_isNeg_173_ = lean_int_dec_lt(v_x_160_, v_intZero_168_);
if (v_isNeg_173_ == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
lean_dec(v_h__3_163_);
v_a_174_ = lean_nat_abs(v_x_160_);
lean_dec(v_x_160_);
v___x_175_ = lean_apply_3(v_h__2_162_, v_a_170_, v_a_174_, lean_box(0));
return v___x_175_;
}
else
{
lean_object* v_one_176_; lean_object* v_n_177_; lean_object* v_abs_178_; lean_object* v_a_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_162_);
v_one_176_ = lean_unsigned_to_nat(1u);
v_n_177_ = lean_nat_sub(v_a_170_, v_one_176_);
lean_dec(v_a_170_);
v_abs_178_ = lean_nat_abs(v_x_160_);
lean_dec(v_x_160_);
v_a_179_ = lean_nat_sub(v_abs_178_, v_one_176_);
lean_dec(v_abs_178_);
v___x_180_ = lean_apply_2(v_h__3_163_, v_n_177_, v_a_179_);
return v___x_180_;
}
}
}
else
{
lean_object* v_abs_181_; lean_object* v_one_182_; lean_object* v_a_183_; uint8_t v_isNeg_184_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
lean_dec(v_h__1_161_);
v_abs_181_ = lean_nat_abs(v_x_159_);
v_one_182_ = lean_unsigned_to_nat(1u);
v_a_183_ = lean_nat_sub(v_abs_181_, v_one_182_);
lean_dec(v_abs_181_);
v_isNeg_184_ = lean_int_dec_lt(v_x_160_, v_intZero_168_);
if (v_isNeg_184_ == 0)
{
lean_object* v_a_185_; uint8_t v_isZero_186_; 
lean_dec(v_h__6_166_);
v_a_185_ = lean_nat_abs(v_x_160_);
lean_dec(v_x_160_);
v_isZero_186_ = lean_nat_dec_eq(v_a_185_, v_natZero_167_);
if (v_isZero_186_ == 1)
{
lean_object* v___x_187_; 
lean_dec(v_a_185_);
lean_dec(v_h__5_165_);
v___x_187_ = lean_apply_1(v_h__4_164_, v_a_183_);
return v___x_187_;
}
else
{
lean_object* v_n_188_; lean_object* v___x_189_; 
lean_dec(v_h__4_164_);
v_n_188_ = lean_nat_sub(v_a_185_, v_one_182_);
lean_dec(v_a_185_);
v___x_189_ = lean_apply_2(v_h__5_165_, v_a_183_, v_n_188_);
return v___x_189_;
}
}
else
{
lean_object* v_abs_190_; lean_object* v_a_191_; lean_object* v___x_192_; 
lean_dec(v_h__5_165_);
lean_dec(v_h__4_164_);
v_abs_190_ = lean_nat_abs(v_x_160_);
lean_dec(v_x_160_);
v_a_191_ = lean_nat_sub(v_abs_190_, v_one_182_);
lean_dec(v_abs_190_);
v___x_192_ = lean_apply_2(v_h__6_166_, v_a_183_, v_a_191_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_, lean_object* v_h__3_198_, lean_object* v_h__4_199_, lean_object* v_h__5_200_, lean_object* v_h__6_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(v_motive_193_, v_x_194_, v_x_195_, v_h__1_196_, v_h__2_197_, v_h__3_198_, v_h__4_199_, v_h__5_200_, v_h__6_201_);
lean_dec(v_x_194_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_bmod_spec__0(lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_nat_to_int(v_a_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Int_bmod___closed__0(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Int_bmod___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(2u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Int_bmod(lean_object* v_x_209_, lean_object* v_m_210_){
_start:
{
lean_object* v___x_211_; lean_object* v_r_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_211_ = lean_nat_to_int(v_m_210_);
v_r_212_ = lean_int_emod(v_x_209_, v___x_211_);
v___x_213_ = lean_obj_once(&l_Int_bmod___closed__0, &l_Int_bmod___closed__0_once, _init_l_Int_bmod___closed__0);
v___x_214_ = lean_int_add(v___x_211_, v___x_213_);
v___x_215_ = lean_obj_once(&l_Int_bmod___closed__1, &l_Int_bmod___closed__1_once, _init_l_Int_bmod___closed__1);
v___x_216_ = lean_int_ediv(v___x_214_, v___x_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_int_dec_lt(v_r_212_, v___x_216_);
lean_dec(v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_int_sub(v_r_212_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v_r_212_);
return v___x_218_;
}
else
{
lean_dec(v___x_211_);
return v_r_212_;
}
}
}
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object* v_x_219_, lean_object* v_m_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Int_bmod(v_x_219_, v_m_220_);
lean_dec(v_x_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object* v_x_222_, lean_object* v_m_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_nat_dec_eq(v_m_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v_q_227_; lean_object* v_r_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_226_ = lean_nat_to_int(v_m_223_);
v_q_227_ = lean_int_ediv(v_x_222_, v___x_226_);
v_r_228_ = lean_int_emod(v_x_222_, v___x_226_);
v___x_229_ = lean_obj_once(&l_Int_bmod___closed__0, &l_Int_bmod___closed__0_once, _init_l_Int_bmod___closed__0);
v___x_230_ = lean_int_add(v___x_226_, v___x_229_);
lean_dec(v___x_226_);
v___x_231_ = lean_obj_once(&l_Int_bmod___closed__1, &l_Int_bmod___closed__1_once, _init_l_Int_bmod___closed__1);
v___x_232_ = lean_int_ediv(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_int_dec_lt(v_r_228_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v_r_228_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_int_add(v_q_227_, v___x_229_);
lean_dec(v_q_227_);
return v___x_234_;
}
else
{
return v_q_227_;
}
}
else
{
lean_object* v___x_235_; 
lean_dec(v_m_223_);
v___x_235_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object* v_x_236_, lean_object* v_m_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Int_bdiv(v_x_236_, v_m_237_);
lean_dec(v_x_236_);
return v_res_238_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_DivMod_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
