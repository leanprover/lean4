// Lean compiler output
// Module: Init.Data.Array.BasicAux
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Set public import Init.Util import Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v_head_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref(v_x_1_);
v___x_8_ = lean_apply_3(v_h__2_4_, v_head_6_, v_tail_7_, v_x_2_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(v_x_11_, v_x_12_, v_h__1_13_, v_h__2_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(lean_object* v_i_16_, lean_object* v_acc_17_, lean_object* v_inst_18_, lean_object* v_f_19_, lean_object* v_as_20_, lean_object* v_b_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(v_i_16_, v_acc_17_, v_inst_18_, v_f_19_, v_as_20_, v_b_21_);
lean_dec(v_i_16_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(lean_object* v_inst_23_, lean_object* v_f_24_, lean_object* v_as_25_, lean_object* v_i_26_, lean_object* v_acc_27_){
_start:
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_array_get_size(v_as_25_);
v___x_29_ = lean_nat_dec_eq(v_i_26_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v_toBind_30_; lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_toBind_30_ = lean_ctor_get(v_inst_23_, 1);
lean_inc(v_toBind_30_);
lean_inc_ref(v_as_25_);
lean_inc(v_f_24_);
lean_inc(v_i_26_);
v___f_31_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_31_, 0, v_i_26_);
lean_closure_set(v___f_31_, 1, v_acc_27_);
lean_closure_set(v___f_31_, 2, v_inst_23_);
lean_closure_set(v___f_31_, 3, v_f_24_);
lean_closure_set(v___f_31_, 4, v_as_25_);
v___x_32_ = lean_array_fget(v_as_25_, v_i_26_);
lean_dec(v_i_26_);
lean_dec_ref(v_as_25_);
v___x_33_ = lean_apply_1(v_f_24_, v___x_32_);
v___x_34_ = lean_apply_4(v_toBind_30_, lean_box(0), lean_box(0), v___x_33_, v___f_31_);
return v___x_34_;
}
else
{
lean_object* v_toApplicative_35_; lean_object* v_toPure_36_; lean_object* v___x_37_; 
lean_dec(v_i_26_);
lean_dec_ref(v_as_25_);
lean_dec(v_f_24_);
v_toApplicative_35_ = lean_ctor_get(v_inst_23_, 0);
lean_inc_ref(v_toApplicative_35_);
lean_dec_ref(v_inst_23_);
v_toPure_36_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_toPure_36_);
lean_dec_ref(v_toApplicative_35_);
v___x_37_ = lean_apply_2(v_toPure_36_, lean_box(0), v_acc_27_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(lean_object* v_i_38_, lean_object* v_acc_39_, lean_object* v_inst_40_, lean_object* v_f_41_, lean_object* v_as_42_, lean_object* v_b_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_i_38_, v___x_44_);
v___x_46_ = lean_array_push(v_acc_39_, v_b_43_);
v___x_47_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_40_, v_f_41_, v_as_42_, v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(lean_object* v_m_48_, lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_f_52_, lean_object* v_as_53_, lean_object* v_i_54_, lean_object* v_acc_55_, lean_object* v_hle_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_51_, v_f_52_, v_as_53_, v_i_54_, v_acc_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___redArg(lean_object* v_inst_58_, lean_object* v_f_59_, lean_object* v_as_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_array_get_size(v_as_60_);
v___x_63_ = lean_mk_empty_array_with_capacity(v___x_62_);
v___x_64_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(v_inst_58_, v_f_59_, v_as_60_, v___x_61_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object* v_m_65_, lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_f_69_, lean_object* v_as_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Array_mapM_x27___redArg(v_inst_68_, v_f_69_, v_as_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(lean_object* v_a_72_, lean_object* v_i_73_, lean_object* v_as_74_, lean_object* v_inst_75_, lean_object* v_f_76_, lean_object* v_b_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(v_a_72_, v_i_73_, v_as_74_, v_inst_75_, v_f_76_, v_b_77_);
lean_dec(v_i_73_);
lean_dec(v_a_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(lean_object* v_inst_79_, lean_object* v_f_80_, lean_object* v_i_81_, lean_object* v_as_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_array_get_size(v_as_82_);
v___x_84_ = lean_nat_dec_lt(v_i_81_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v_toApplicative_85_; lean_object* v_toPure_86_; lean_object* v___x_87_; 
lean_dec(v_i_81_);
lean_dec(v_f_80_);
v_toApplicative_85_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toApplicative_85_);
lean_dec_ref(v_inst_79_);
v_toPure_86_ = lean_ctor_get(v_toApplicative_85_, 1);
lean_inc(v_toPure_86_);
lean_dec_ref(v_toApplicative_85_);
v___x_87_ = lean_apply_2(v_toPure_86_, lean_box(0), v_as_82_);
return v___x_87_;
}
else
{
lean_object* v_toBind_88_; lean_object* v_a_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_toBind_88_ = lean_ctor_get(v_inst_79_, 1);
lean_inc(v_toBind_88_);
v_a_89_ = lean_array_fget(v_as_82_, v_i_81_);
lean_inc(v_f_80_);
lean_inc(v_a_89_);
v___f_90_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_90_, 0, v_a_89_);
lean_closure_set(v___f_90_, 1, v_i_81_);
lean_closure_set(v___f_90_, 2, v_as_82_);
lean_closure_set(v___f_90_, 3, v_inst_79_);
lean_closure_set(v___f_90_, 4, v_f_80_);
v___x_91_ = lean_apply_1(v_f_80_, v_a_89_);
v___x_92_ = lean_apply_4(v_toBind_88_, lean_box(0), lean_box(0), v___x_91_, v___f_90_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(lean_object* v_a_93_, lean_object* v_i_94_, lean_object* v_as_95_, lean_object* v_inst_96_, lean_object* v_f_97_, lean_object* v_b_98_){
_start:
{
size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_ptr_addr(v_a_93_);
v___x_100_ = lean_ptr_addr(v_b_98_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_i_94_, v___x_102_);
v___x_104_ = lean_array_fset(v_as_95_, v_i_94_, v_b_98_);
v___x_105_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_96_, v_f_97_, v___x_103_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_b_98_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_i_94_, v___x_106_);
v___x_108_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_96_, v_f_97_, v___x_107_, v_as_95_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object* v_m_109_, lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_f_112_, lean_object* v_i_113_, lean_object* v_as_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_111_, v_f_112_, v_i_113_, v_as_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(lean_object* v_inst_116_, lean_object* v_as_117_, lean_object* v_f_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_116_, v_f_118_, v___x_119_, v_as_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object* v_m_121_, lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_as_124_, lean_object* v_f_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v_inst_123_, v_f_125_, v___x_126_, v_as_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg___lam__0(lean_object* v_f_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_1(v_f_128_, v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg(lean_object* v_as_150_, lean_object* v_f_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___f_152_ = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(v___f_152_, 0, v_f_151_);
v___x_153_ = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v___x_153_, v___f_152_, v___x_154_, v_as_150_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono(lean_object* v_00_u03b1_156_, lean_object* v_as_157_, lean_object* v_f_158_){
_start:
{
lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___f_159_ = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(v___f_159_, 0, v_f_158_);
v___x_160_ = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(v___x_160_, v___f_159_, v___x_161_, v_as_157_);
return v___x_162_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* runtime_initialize_Init_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
