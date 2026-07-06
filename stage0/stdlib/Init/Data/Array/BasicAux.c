// Lean compiler output
// Module: Init.Data.Array.BasicAux
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Set public import Init.Util import Init.Data.Nat.Internal.Linear
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMono___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__0 = (const lean_object*)&l_Array_mapMono___redArg___closed__0_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__1 = (const lean_object*)&l_Array_mapMono___redArg___closed__1_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__2 = (const lean_object*)&l_Array_mapMono___redArg___closed__2_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__3 = (const lean_object*)&l_Array_mapMono___redArg___closed__3_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__4 = (const lean_object*)&l_Array_mapMono___redArg___closed__4_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__5 = (const lean_object*)&l_Array_mapMono___redArg___closed__5_value;
static const lean_closure_object l_Array_mapMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__6 = (const lean_object*)&l_Array_mapMono___redArg___closed__6_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__0_value),((lean_object*)&l_Array_mapMono___redArg___closed__1_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__7 = (const lean_object*)&l_Array_mapMono___redArg___closed__7_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__7_value),((lean_object*)&l_Array_mapMono___redArg___closed__2_value),((lean_object*)&l_Array_mapMono___redArg___closed__3_value),((lean_object*)&l_Array_mapMono___redArg___closed__4_value),((lean_object*)&l_Array_mapMono___redArg___closed__5_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__8 = (const lean_object*)&l_Array_mapMono___redArg___closed__8_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__8_value),((lean_object*)&l_Array_mapMono___redArg___closed__6_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__9 = (const lean_object*)&l_Array_mapMono___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_mapMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMono(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(lean_object* v_i_1_, lean_object* v_acc_2_, lean_object* v_inst_3_, lean_object* v_f_4_, lean_object* v_as_5_, lean_object* v_b_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(v_i_1_, v_acc_2_, v_inst_3_, v_f_4_, v_as_5_, v_b_6_);
lean_dec(v_i_1_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(lean_object* v_inst_8_, lean_object* v_f_9_, lean_object* v_as_10_, lean_object* v_i_11_, lean_object* v_acc_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_array_get_size(v_as_10_);
v___x_14_ = lean_nat_dec_eq(v_i_11_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v_toBind_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_toBind_15_ = lean_ctor_get(v_inst_8_, 1);
lean_inc(v_toBind_15_);
lean_inc_ref(v_as_10_);
lean_inc(v_f_9_);
lean_inc(v_i_11_);
v___f_16_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_16_, 0, v_i_11_);
lean_closure_set(v___f_16_, 1, v_acc_12_);
lean_closure_set(v___f_16_, 2, v_inst_8_);
lean_closure_set(v___f_16_, 3, v_f_9_);
lean_closure_set(v___f_16_, 4, v_as_10_);
v___x_17_ = lean_array_fget(v_as_10_, v_i_11_);
lean_dec(v_i_11_);
lean_dec_ref(v_as_10_);
v___x_18_ = lean_apply_1(v_f_9_, v___x_17_);
v___x_19_ = lean_apply_4(v_toBind_15_, lean_box(0), lean_box(0), v___x_18_, v___f_16_);
return v___x_19_;
}
else
{
lean_object* v_toApplicative_20_; lean_object* v_toPure_21_; lean_object* v___x_22_; 
lean_dec(v_i_11_);
lean_dec_ref(v_as_10_);
lean_dec(v_f_9_);
v_toApplicative_20_ = lean_ctor_get(v_inst_8_, 0);
lean_inc_ref(v_toApplicative_20_);
lean_dec_ref(v_inst_8_);
v_toPure_21_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_21_);
lean_dec_ref(v_toApplicative_20_);
v___x_22_ = lean_apply_2(v_toPure_21_, lean_box(0), v_acc_12_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(lean_object* v_i_23_, lean_object* v_acc_24_, lean_object* v_inst_25_, lean_object* v_f_26_, lean_object* v_as_27_, lean_object* v_b_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v_i_23_, v___x_29_);
v___x_31_ = lean_array_push(v_acc_24_, v_b_28_);
v___x_32_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_25_, v_f_26_, v_as_27_, v___x_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(lean_object* v_m_33_, lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_inst_36_, lean_object* v_f_37_, lean_object* v_as_38_, lean_object* v_i_39_, lean_object* v_acc_40_, lean_object* v_hle_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_36_, v_f_37_, v_as_38_, v_i_39_, v_acc_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___redArg(lean_object* v_inst_43_, lean_object* v_f_44_, lean_object* v_as_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_array_get_size(v_as_45_);
v___x_48_ = lean_mk_empty_array_with_capacity(v___x_47_);
v___x_49_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_43_, v_f_44_, v_as_45_, v___x_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object* v_m_50_, lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_inst_53_, lean_object* v_f_54_, lean_object* v_as_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Array_mapM_x27___redArg(v_inst_53_, v_f_54_, v_as_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(lean_object* v_a_57_, lean_object* v_i_58_, lean_object* v_as_59_, lean_object* v_inst_60_, lean_object* v_f_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(v_a_57_, v_i_58_, v_as_59_, v_inst_60_, v_f_61_, v_b_62_);
lean_dec(v_i_58_);
lean_dec(v_a_57_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(lean_object* v_inst_64_, lean_object* v_f_65_, lean_object* v_i_66_, lean_object* v_as_67_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_array_get_size(v_as_67_);
v___x_69_ = lean_nat_dec_lt(v_i_66_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v_toApplicative_70_; lean_object* v_toPure_71_; lean_object* v___x_72_; 
lean_dec(v_i_66_);
lean_dec(v_f_65_);
v_toApplicative_70_ = lean_ctor_get(v_inst_64_, 0);
lean_inc_ref(v_toApplicative_70_);
lean_dec_ref(v_inst_64_);
v_toPure_71_ = lean_ctor_get(v_toApplicative_70_, 1);
lean_inc(v_toPure_71_);
lean_dec_ref(v_toApplicative_70_);
v___x_72_ = lean_apply_2(v_toPure_71_, lean_box(0), v_as_67_);
return v___x_72_;
}
else
{
lean_object* v_toBind_73_; lean_object* v_a_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_toBind_73_ = lean_ctor_get(v_inst_64_, 1);
lean_inc(v_toBind_73_);
v_a_74_ = lean_array_fget(v_as_67_, v_i_66_);
lean_inc(v_f_65_);
lean_inc(v_a_74_);
v___f_75_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_75_, 0, v_a_74_);
lean_closure_set(v___f_75_, 1, v_i_66_);
lean_closure_set(v___f_75_, 2, v_as_67_);
lean_closure_set(v___f_75_, 3, v_inst_64_);
lean_closure_set(v___f_75_, 4, v_f_65_);
v___x_76_ = lean_apply_1(v_f_65_, v_a_74_);
v___x_77_ = lean_apply_4(v_toBind_73_, lean_box(0), lean_box(0), v___x_76_, v___f_75_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(lean_object* v_a_78_, lean_object* v_i_79_, lean_object* v_as_80_, lean_object* v_inst_81_, lean_object* v_f_82_, lean_object* v_b_83_){
_start:
{
size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_ptr_addr(v_a_78_);
v___x_85_ = lean_ptr_addr(v_b_83_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_79_, v___x_87_);
v___x_89_ = lean_array_fset(v_as_80_, v_i_79_, v_b_83_);
v___x_90_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_81_, v_f_82_, v___x_88_, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_b_83_);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_i_79_, v___x_91_);
v___x_93_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_81_, v_f_82_, v___x_92_, v_as_80_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object* v_m_94_, lean_object* v_00_u03b1_95_, lean_object* v_inst_96_, lean_object* v_f_97_, lean_object* v_i_98_, lean_object* v_as_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_96_, v_f_97_, v_i_98_, v_as_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(lean_object* v_inst_101_, lean_object* v_as_102_, lean_object* v_f_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_101_, v_f_103_, v___x_104_, v_as_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object* v_m_106_, lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_as_109_, lean_object* v_f_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_108_, v_f_110_, v___x_111_, v_as_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg___lam__0(lean_object* v_f_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_apply_1(v_f_113_, v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg(lean_object* v_as_135_, lean_object* v_f_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___f_137_ = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(v___f_137_, 0, v_f_136_);
v___x_138_ = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v___x_138_, v___f_137_, v___x_139_, v_as_135_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono(lean_object* v_00_u03b1_141_, lean_object* v_as_142_, lean_object* v_f_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___f_144_ = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(v___f_144_, 0, v_f_143_);
v___x_145_ = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v___x_145_, v___f_144_, v___x_146_, v_as_142_);
return v___x_147_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif
