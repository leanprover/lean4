// Lean compiler output
// Module: Init.Data.List.SplitOn.Basic
// Imports: public import Init.Data.List.Basic public import Init.NotationExtra import Init.Data.Array.Bootstrap import Init.Data.List.Lemmas
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value;
static const lean_array_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOnPTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOnPTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_splitOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v_x1_1_);
lean_ctor_set(v___x_3_, 1, v_x2_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(lean_object* v_p_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
if (lean_obj_tag(v_a_27_) == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
lean_dec_ref(v_p_26_);
v___x_30_ = lean_array_to_list(v_a_28_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = lean_array_get_size(v_a_29_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9));
v___x_36_ = lean_nat_dec_lt(v___x_34_, v___x_33_);
if (v___x_36_ == 0)
{
lean_dec_ref(v_a_29_);
return v___x_32_;
}
else
{
lean_object* v___f_37_; size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; 
v___f_37_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10));
v___x_38_ = lean_usize_of_nat(v___x_33_);
v___x_39_ = ((size_t)0ULL);
v___x_40_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_35_, v___f_37_, v_a_29_, v___x_38_, v___x_39_, v___x_32_);
return v___x_40_;
}
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_head_41_ = lean_ctor_get(v_a_27_, 0);
lean_inc_n(v_head_41_, 2);
v_tail_42_ = lean_ctor_get(v_a_27_, 1);
lean_inc(v_tail_42_);
lean_dec_ref(v_a_27_);
lean_inc_ref(v_p_26_);
v___x_43_ = lean_apply_1(v_p_26_, v_head_41_);
v___x_44_ = lean_unbox(v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
v___x_45_ = lean_array_push(v_a_28_, v_head_41_);
v_a_27_ = v_tail_42_;
v_a_28_ = v___x_45_;
goto _start;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_head_41_);
v___x_47_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
v___x_48_ = lean_array_to_list(v_a_28_);
v___x_49_ = lean_array_push(v_a_29_, v___x_48_);
v_a_27_ = v_tail_42_;
v_a_28_ = v___x_47_;
v_a_29_ = v___x_49_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(lean_object* v_00_u03b1_51_, lean_object* v_p_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(v_p_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_List_splitOnPTR___redArg(lean_object* v_p_57_, lean_object* v_l_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
v___x_60_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(v_p_57_, v_l_58_, v___x_59_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_List_splitOnPTR(lean_object* v_00_u03b1_61_, lean_object* v_p_62_, lean_object* v_l_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
v___x_65_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(v_p_62_, v_l_63_, v___x_64_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_70_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_apply_1(v_h__1_68_, v_x_67_);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_68_);
v_head_71_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_head_71_);
v_tail_72_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_tail_72_);
lean_dec_ref(v_x_66_);
v___x_73_ = lean_apply_3(v_h__2_69_, v_head_71_, v_tail_72_, v_x_67_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(lean_object* v_00_u03b1_74_, lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_80_; 
lean_dec(v_h__2_79_);
v___x_80_ = lean_apply_1(v_h__1_78_, v_x_77_);
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_78_);
v_head_81_ = lean_ctor_get(v_x_76_, 0);
lean_inc(v_head_81_);
v_tail_82_ = lean_ctor_get(v_x_76_, 1);
lean_inc(v_tail_82_);
lean_dec_ref(v_x_76_);
v___x_83_ = lean_apply_3(v_h__2_79_, v_head_81_, v_tail_82_, v_x_77_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_89_; 
lean_dec(v_h__2_88_);
v___x_89_ = lean_apply_2(v_h__1_87_, v_x_85_, v_x_86_);
return v___x_89_;
}
else
{
lean_object* v_head_90_; lean_object* v_tail_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_87_);
v_head_90_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_head_90_);
v_tail_91_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_tail_91_);
lean_dec_ref(v_x_84_);
v___x_92_ = lean_apply_4(v_h__2_88_, v_head_90_, v_tail_91_, v_x_85_, v_x_86_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(lean_object* v_00_u03b1_93_, lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v___x_100_; 
lean_dec(v_h__2_99_);
v___x_100_ = lean_apply_2(v_h__1_98_, v_x_96_, v_x_97_);
return v___x_100_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_103_; 
lean_dec(v_h__1_98_);
v_head_101_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_head_101_);
v_tail_102_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_tail_102_);
lean_dec_ref(v_x_95_);
v___x_103_ = lean_apply_4(v_h__2_99_, v_head_101_, v_tail_102_, v_x_96_, v_x_97_);
return v___x_103_;
}
}
}
LEAN_EXPORT uint8_t l_List_splitOn___redArg___lam__0(lean_object* v_inst_104_, lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_apply_2(v_inst_104_, v_x_106_, v_a_105_);
v___x_108_ = lean_unbox(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_List_splitOn___redArg___lam__0___boxed(lean_object* v_inst_109_, lean_object* v_a_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_List_splitOn___redArg___lam__0(v_inst_109_, v_a_110_, v_x_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_List_splitOn___redArg(lean_object* v_inst_114_, lean_object* v_a_115_, lean_object* v_as_116_){
_start:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___f_117_ = lean_alloc_closure((void*)(l_List_splitOn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_117_, 0, v_inst_114_);
lean_closure_set(v___f_117_, 1, v_a_115_);
v___x_118_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
v___x_119_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(v___f_117_, v_as_116_, v___x_118_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_List_splitOn(lean_object* v_00_u03b1_120_, lean_object* v_inst_121_, lean_object* v_a_122_, lean_object* v_as_123_){
_start:
{
lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___f_124_ = lean_alloc_closure((void*)(l_List_splitOn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_124_, 0, v_inst_121_);
lean_closure_set(v___f_124_, 1, v_a_122_);
v___x_125_ = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
v___x_126_ = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(v___f_124_, v_as_123_, v___x_125_, v___x_125_);
return v___x_126_;
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_SplitOn_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_SplitOn_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
