// Lean compiler output
// Module: Init.Data.List.Control
// Imports: public import Init.Control.Lawful
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapA___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_List_mapA___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_mapA___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_mapA___redArg___closed__0 = (const lean_object*)&l_List_mapA___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapA___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapA___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forA___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forA___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_zipWithM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_zipWithM___redArg___closed__0 = (const lean_object*)&l_List_zipWithM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_zipWithM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_filterAuxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterRevM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_instForMOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instFunctor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instFunctor___closed__0 = (const lean_object*)&l_List_instFunctor___closed__0_value;
static const lean_closure_object l_List_instFunctor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_mapTR, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instFunctor___closed__1 = (const lean_object*)&l_List_instFunctor___closed__1_value;
static const lean_ctor_object l_List_instFunctor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_instFunctor___closed__1_value),((lean_object*)&l_List_instFunctor___closed__0_value)}};
static const lean_object* l_List_instFunctor___closed__2 = (const lean_object*)&l_List_instFunctor___closed__2_value;
LEAN_EXPORT const lean_object* l_List_instFunctor = (const lean_object*)&l_List_instFunctor___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___redArg(lean_object* v_inst_1_, lean_object* v_f_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_toApplicative_5_; lean_object* v_toPure_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_toApplicative_5_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_5_);
lean_dec(v_f_2_);
lean_dec_ref(v_inst_1_);
v_toPure_6_ = lean_ctor_get(v_toApplicative_5_, 1);
lean_inc(v_toPure_6_);
lean_dec_ref(v_toApplicative_5_);
v___x_7_ = l_List_reverse___redArg(v_x_4_);
v___x_8_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_7_);
return v___x_8_;
}
else
{
lean_object* v_toBind_9_; lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_toBind_9_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_toBind_9_);
v_head_10_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_10_);
v_tail_11_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_11_);
lean_dec_ref_known(v_x_3_, 2);
lean_inc(v_f_2_);
v___f_12_ = lean_alloc_closure((void*)(l_List_mapM_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_12_, 0, v_x_4_);
lean_closure_set(v___f_12_, 1, v_inst_1_);
lean_closure_set(v___f_12_, 2, v_f_2_);
lean_closure_set(v___f_12_, 3, v_tail_11_);
v___x_13_ = lean_apply_1(v_f_2_, v_head_10_);
v___x_14_ = lean_apply_4(v_toBind_9_, lean_box(0), lean_box(0), v___x_13_, v___f_12_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___redArg___lam__0(lean_object* v_x_15_, lean_object* v_inst_16_, lean_object* v_f_17_, lean_object* v_tail_18_, lean_object* v_____do__lift_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v_____do__lift_19_);
lean_ctor_set(v___x_20_, 1, v_x_15_);
v___x_21_ = l_List_mapM_loop___redArg(v_inst_16_, v_f_17_, v_tail_18_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop(lean_object* v_m_22_, lean_object* v_inst_23_, lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_f_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_List_mapM_loop___redArg(v_inst_23_, v_f_26_, v_x_27_, v_x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_List_mapM___redArg(lean_object* v_inst_30_, lean_object* v_f_31_, lean_object* v_as_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_box(0);
v___x_34_ = l_List_mapM_loop___redArg(v_inst_30_, v_f_31_, v_as_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_List_mapM(lean_object* v_m_35_, lean_object* v_inst_36_, lean_object* v_00_u03b1_37_, lean_object* v_00_u03b2_38_, lean_object* v_f_39_, lean_object* v_as_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = l_List_mapM_loop___redArg(v_inst_36_, v_f_39_, v_as_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_List_mapA___redArg___lam__0(lean_object* v_head_43_, lean_object* v_tail_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v_head_43_);
lean_ctor_set(v___x_45_, 1, v_tail_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_List_mapA___redArg(lean_object* v_inst_47_, lean_object* v_f_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_toPure_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_f_48_);
v_toPure_50_ = lean_ctor_get(v_inst_47_, 1);
lean_inc(v_toPure_50_);
lean_dec_ref(v_inst_47_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_2(v_toPure_50_, lean_box(0), v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_toFunctor_53_; lean_object* v_toSeq_54_; lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v_map_57_; lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_toFunctor_53_ = lean_ctor_get(v_inst_47_, 0);
v_toSeq_54_ = lean_ctor_get(v_inst_47_, 2);
lean_inc(v_toSeq_54_);
v_head_55_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_head_55_);
v_tail_56_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_tail_56_);
lean_dec_ref_known(v_x_49_, 2);
v_map_57_ = lean_ctor_get(v_toFunctor_53_, 0);
lean_inc(v_map_57_);
v___f_58_ = ((lean_object*)(l_List_mapA___redArg___closed__0));
lean_inc(v_f_48_);
v___f_59_ = lean_alloc_closure((void*)(l_List_mapA___redArg___lam__1), 4, 3);
lean_closure_set(v___f_59_, 0, v_inst_47_);
lean_closure_set(v___f_59_, 1, v_f_48_);
lean_closure_set(v___f_59_, 2, v_tail_56_);
v___x_60_ = lean_apply_1(v_f_48_, v_head_55_);
v___x_61_ = lean_apply_4(v_map_57_, lean_box(0), lean_box(0), v___f_58_, v___x_60_);
v___x_62_ = lean_apply_4(v_toSeq_54_, lean_box(0), lean_box(0), v___x_61_, v___f_59_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapA___redArg___lam__1(lean_object* v_inst_63_, lean_object* v_f_64_, lean_object* v_tail_65_, lean_object* v_x_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_List_mapA___redArg(v_inst_63_, v_f_64_, v_tail_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_List_mapA(lean_object* v_m_68_, lean_object* v_inst_69_, lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_f_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_List_mapA___redArg(v_inst_69_, v_f_72_, v_x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_List_forM___redArg(lean_object* v_inst_75_, lean_object* v_as_76_, lean_object* v_f_77_){
_start:
{
if (lean_obj_tag(v_as_76_) == 0)
{
lean_object* v_toApplicative_78_; lean_object* v_toPure_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_toApplicative_78_ = lean_ctor_get(v_inst_75_, 0);
lean_inc_ref(v_toApplicative_78_);
lean_dec(v_f_77_);
lean_dec_ref(v_inst_75_);
v_toPure_79_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_79_);
lean_dec_ref(v_toApplicative_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_2(v_toPure_79_, lean_box(0), v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_toBind_82_; lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_toBind_82_ = lean_ctor_get(v_inst_75_, 1);
lean_inc(v_toBind_82_);
v_head_83_ = lean_ctor_get(v_as_76_, 0);
lean_inc(v_head_83_);
v_tail_84_ = lean_ctor_get(v_as_76_, 1);
lean_inc(v_tail_84_);
lean_dec_ref_known(v_as_76_, 2);
lean_inc(v_f_77_);
v___f_85_ = lean_alloc_closure((void*)(l_List_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_85_, 0, v_inst_75_);
lean_closure_set(v___f_85_, 1, v_tail_84_);
lean_closure_set(v___f_85_, 2, v_f_77_);
v___x_86_ = lean_apply_1(v_f_77_, v_head_83_);
v___x_87_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v___x_86_, v___f_85_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___redArg___lam__0(lean_object* v_inst_88_, lean_object* v_tail_89_, lean_object* v_f_90_, lean_object* v_____r_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_List_forM___redArg(v_inst_88_, v_tail_89_, v_f_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_List_forM(lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_00_u03b1_95_, lean_object* v_as_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_List_forM___redArg(v_inst_94_, v_as_96_, v_f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_List_forA___redArg(lean_object* v_inst_99_, lean_object* v_as_100_, lean_object* v_f_101_){
_start:
{
if (lean_obj_tag(v_as_100_) == 0)
{
lean_object* v_toPure_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_f_101_);
v_toPure_102_ = lean_ctor_get(v_inst_99_, 1);
lean_inc(v_toPure_102_);
lean_dec_ref(v_inst_99_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_2(v_toPure_102_, lean_box(0), v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_toSeqRight_105_; lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_toSeqRight_105_ = lean_ctor_get(v_inst_99_, 4);
lean_inc(v_toSeqRight_105_);
v_head_106_ = lean_ctor_get(v_as_100_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_as_100_, 1);
lean_inc(v_tail_107_);
lean_dec_ref_known(v_as_100_, 2);
lean_inc(v_f_101_);
v___f_108_ = lean_alloc_closure((void*)(l_List_forA___redArg___lam__0), 4, 3);
lean_closure_set(v___f_108_, 0, v_inst_99_);
lean_closure_set(v___f_108_, 1, v_tail_107_);
lean_closure_set(v___f_108_, 2, v_f_101_);
v___x_109_ = lean_apply_1(v_f_101_, v_head_106_);
v___x_110_ = lean_apply_4(v_toSeqRight_105_, lean_box(0), lean_box(0), v___x_109_, v___f_108_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_List_forA___redArg___lam__0(lean_object* v_inst_111_, lean_object* v_tail_112_, lean_object* v_f_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_List_forA___redArg(v_inst_111_, v_tail_112_, v_f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_List_forA(lean_object* v_m_116_, lean_object* v_inst_117_, lean_object* v_00_u03b1_118_, lean_object* v_as_119_, lean_object* v_f_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_List_forA___redArg(v_inst_117_, v_as_119_, v_f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_loop___redArg(lean_object* v_inst_122_, lean_object* v_f_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_toApplicative_127_; lean_object* v_toBind_128_; lean_object* v_toPure_129_; lean_object* v_acc_131_; 
v_toApplicative_127_ = lean_ctor_get(v_inst_122_, 0);
v_toBind_128_ = lean_ctor_get(v_inst_122_, 1);
lean_inc(v_toBind_128_);
v_toPure_129_ = lean_ctor_get(v_toApplicative_127_, 1);
if (lean_obj_tag(v_x_124_) == 1)
{
if (lean_obj_tag(v_x_125_) == 1)
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_head_134_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_head_134_);
v_tail_135_ = lean_ctor_get(v_x_124_, 1);
lean_inc(v_tail_135_);
lean_dec_ref_known(v_x_124_, 2);
v_head_136_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_head_136_);
v_tail_137_ = lean_ctor_get(v_x_125_, 1);
lean_inc(v_tail_137_);
lean_dec_ref_known(v_x_125_, 2);
lean_inc(v_f_123_);
v___f_138_ = lean_alloc_closure((void*)(l_List_zipWithM_loop___redArg___lam__0), 6, 5);
lean_closure_set(v___f_138_, 0, v_x_126_);
lean_closure_set(v___f_138_, 1, v_inst_122_);
lean_closure_set(v___f_138_, 2, v_f_123_);
lean_closure_set(v___f_138_, 3, v_tail_135_);
lean_closure_set(v___f_138_, 4, v_tail_137_);
v___x_139_ = lean_apply_2(v_f_123_, v_head_134_, v_head_136_);
v___x_140_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_139_, v___f_138_);
return v___x_140_;
}
else
{
lean_inc(v_toPure_129_);
lean_dec_ref_known(v_x_124_, 2);
lean_dec(v_toBind_128_);
lean_dec(v_x_125_);
lean_dec(v_f_123_);
lean_dec_ref(v_inst_122_);
v_acc_131_ = v_x_126_;
goto v___jp_130_;
}
}
else
{
lean_inc(v_toPure_129_);
lean_dec(v_toBind_128_);
lean_dec(v_x_125_);
lean_dec(v_x_124_);
lean_dec(v_f_123_);
lean_dec_ref(v_inst_122_);
v_acc_131_ = v_x_126_;
goto v___jp_130_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_array_to_list(v_acc_131_);
v___x_133_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_loop___redArg___lam__0(lean_object* v_x_141_, lean_object* v_inst_142_, lean_object* v_f_143_, lean_object* v_tail_144_, lean_object* v_tail_145_, lean_object* v_____do__lift_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_array_push(v_x_141_, v_____do__lift_146_);
v___x_148_ = l_List_zipWithM_loop___redArg(v_inst_142_, v_f_143_, v_tail_144_, v_tail_145_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM_loop(lean_object* v_m_149_, lean_object* v_inst_150_, lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_00_u03b3_153_, lean_object* v_f_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_List_zipWithM_loop___redArg(v_inst_150_, v_f_154_, v_x_155_, v_x_156_, v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM___redArg(lean_object* v_inst_161_, lean_object* v_f_162_, lean_object* v_as_163_, lean_object* v_bs_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_List_zipWithM___redArg___closed__0));
v___x_166_ = l_List_zipWithM_loop___redArg(v_inst_161_, v_f_162_, v_as_163_, v_bs_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithM(lean_object* v_m_167_, lean_object* v_inst_168_, lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_00_u03b3_171_, lean_object* v_f_172_, lean_object* v_as_173_, lean_object* v_bs_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_List_zipWithM___redArg___closed__0));
v___x_176_ = l_List_zipWithM_loop___redArg(v_inst_168_, v_f_172_, v_as_173_, v_bs_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg___lam__0___boxed(lean_object* v_inst_177_, lean_object* v_f_178_, lean_object* v_tail_179_, lean_object* v_x_180_, lean_object* v_head_181_, lean_object* v_b_182_){
_start:
{
uint8_t v_b_boxed_183_; lean_object* v_res_184_; 
v_b_boxed_183_ = lean_unbox(v_b_182_);
v_res_184_ = l_List_filterAuxM___redArg___lam__0(v_inst_177_, v_f_178_, v_tail_179_, v_x_180_, v_head_181_, v_b_boxed_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg(lean_object* v_inst_185_, lean_object* v_f_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_toApplicative_189_; lean_object* v_toPure_190_; lean_object* v___x_191_; 
v_toApplicative_189_ = lean_ctor_get(v_inst_185_, 0);
lean_inc_ref(v_toApplicative_189_);
lean_dec(v_f_186_);
lean_dec_ref(v_inst_185_);
v_toPure_190_ = lean_ctor_get(v_toApplicative_189_, 1);
lean_inc(v_toPure_190_);
lean_dec_ref(v_toApplicative_189_);
v___x_191_ = lean_apply_2(v_toPure_190_, lean_box(0), v_x_188_);
return v___x_191_;
}
else
{
lean_object* v_toBind_192_; lean_object* v_head_193_; lean_object* v_tail_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_toBind_192_ = lean_ctor_get(v_inst_185_, 1);
lean_inc(v_toBind_192_);
v_head_193_ = lean_ctor_get(v_x_187_, 0);
lean_inc_n(v_head_193_, 2);
v_tail_194_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_tail_194_);
lean_dec_ref_known(v_x_187_, 2);
lean_inc(v_f_186_);
v___f_195_ = lean_alloc_closure((void*)(l_List_filterAuxM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_195_, 0, v_inst_185_);
lean_closure_set(v___f_195_, 1, v_f_186_);
lean_closure_set(v___f_195_, 2, v_tail_194_);
lean_closure_set(v___f_195_, 3, v_x_188_);
lean_closure_set(v___f_195_, 4, v_head_193_);
v___x_196_ = lean_apply_1(v_f_186_, v_head_193_);
v___x_197_ = lean_apply_4(v_toBind_192_, lean_box(0), lean_box(0), v___x_196_, v___f_195_);
return v___x_197_;
}
}
}
lean_object* l_List_filterAuxM___redArg___lam__0(lean_object* v_inst_198_, lean_object* v_f_199_, lean_object* v_tail_200_, lean_object* v_x_201_, lean_object* v_head_202_, uint8_t v_b_203_){
_start:
{
if (v_b_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_head_202_);
v___x_204_ = l_List_filterAuxM___redArg(v_inst_198_, v_f_199_, v_tail_200_, v_x_201_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v_head_202_);
lean_ctor_set(v___x_205_, 1, v_x_201_);
v___x_206_ = l_List_filterAuxM___redArg(v_inst_198_, v_f_199_, v_tail_200_, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT void l_List_filterAuxM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_198_ = stack[0].m_obj;
lean_object* v_f_199_ = stack[1].m_obj;
lean_object* v_tail_200_ = stack[2].m_obj;
lean_object* v_x_201_ = stack[3].m_obj;
lean_object* v_head_202_ = stack[4].m_obj;
uint8_t v_b_203_ = stack[5].m_num;
lean_object* v_res_207_;
v_res_207_ = l_List_filterAuxM___redArg___lam__0(v_inst_198_, v_f_199_, v_tail_200_, v_x_201_, v_head_202_, v_b_203_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM(lean_object* v_m_208_, lean_object* v_inst_209_, lean_object* v_00_u03b1_210_, lean_object* v_f_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_List_filterAuxM___redArg(v_inst_209_, v_f_211_, v_x_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_List_filterM___redArg___lam__0(lean_object* v_toPure_215_, lean_object* v_as_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = l_List_reverse___redArg(v_as_216_);
v___x_218_ = lean_apply_2(v_toPure_215_, lean_box(0), v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_List_filterM___redArg(lean_object* v_inst_219_, lean_object* v_p_220_, lean_object* v_as_221_){
_start:
{
lean_object* v_toApplicative_222_; lean_object* v_toBind_223_; lean_object* v_toPure_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_228_; 
v_toApplicative_222_ = lean_ctor_get(v_inst_219_, 0);
v_toBind_223_ = lean_ctor_get(v_inst_219_, 1);
lean_inc(v_toBind_223_);
v_toPure_224_ = lean_ctor_get(v_toApplicative_222_, 1);
lean_inc(v_toPure_224_);
v___x_225_ = lean_box(0);
v___x_226_ = l_List_filterAuxM___redArg(v_inst_219_, v_p_220_, v_as_221_, v___x_225_);
v___f_227_ = lean_alloc_closure((void*)(l_List_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_227_, 0, v_toPure_224_);
v___x_228_ = lean_apply_4(v_toBind_223_, lean_box(0), lean_box(0), v___x_226_, v___f_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_List_filterM(lean_object* v_m_229_, lean_object* v_inst_230_, lean_object* v_00_u03b1_231_, lean_object* v_p_232_, lean_object* v_as_233_){
_start:
{
lean_object* v_toApplicative_234_; lean_object* v_toBind_235_; lean_object* v_toPure_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___f_239_; lean_object* v___x_240_; 
v_toApplicative_234_ = lean_ctor_get(v_inst_230_, 0);
v_toBind_235_ = lean_ctor_get(v_inst_230_, 1);
lean_inc(v_toBind_235_);
v_toPure_236_ = lean_ctor_get(v_toApplicative_234_, 1);
lean_inc(v_toPure_236_);
v___x_237_ = lean_box(0);
v___x_238_ = l_List_filterAuxM___redArg(v_inst_230_, v_p_232_, v_as_233_, v___x_237_);
v___f_239_ = lean_alloc_closure((void*)(l_List_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_239_, 0, v_toPure_236_);
v___x_240_ = lean_apply_4(v_toBind_235_, lean_box(0), lean_box(0), v___x_238_, v___f_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_List_filterRevM___redArg(lean_object* v_inst_241_, lean_object* v_p_242_, lean_object* v_as_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = l_List_reverse___redArg(v_as_243_);
v___x_245_ = lean_box(0);
v___x_246_ = l_List_filterAuxM___redArg(v_inst_241_, v_p_242_, v___x_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_List_filterRevM(lean_object* v_m_247_, lean_object* v_inst_248_, lean_object* v_00_u03b1_249_, lean_object* v_p_250_, lean_object* v_as_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = l_List_reverse___redArg(v_as_251_);
v___x_253_ = lean_box(0);
v___x_254_ = l_List_filterAuxM___redArg(v_inst_248_, v_p_250_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0___boxed(lean_object* v_inst_255_, lean_object* v_f_256_, lean_object* v_tail_257_, lean_object* v_x_258_, lean_object* v_____do__lift_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_List_filterMapM_loop___redArg___lam__0(v_inst_255_, v_f_256_, v_tail_257_, v_x_258_, v_____do__lift_259_);
lean_dec(v_____do__lift_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg(lean_object* v_inst_261_, lean_object* v_f_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_toApplicative_265_; lean_object* v_toPure_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_toApplicative_265_ = lean_ctor_get(v_inst_261_, 0);
lean_inc_ref(v_toApplicative_265_);
lean_dec(v_f_262_);
lean_dec_ref(v_inst_261_);
v_toPure_266_ = lean_ctor_get(v_toApplicative_265_, 1);
lean_inc(v_toPure_266_);
lean_dec_ref(v_toApplicative_265_);
v___x_267_ = l_List_reverse___redArg(v_x_264_);
v___x_268_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_toBind_269_; lean_object* v_head_270_; lean_object* v_tail_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_toBind_269_ = lean_ctor_get(v_inst_261_, 1);
lean_inc(v_toBind_269_);
v_head_270_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_head_270_);
v_tail_271_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_tail_271_);
lean_dec_ref_known(v_x_263_, 2);
lean_inc(v_f_262_);
v___f_272_ = lean_alloc_closure((void*)(l_List_filterMapM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_272_, 0, v_inst_261_);
lean_closure_set(v___f_272_, 1, v_f_262_);
lean_closure_set(v___f_272_, 2, v_tail_271_);
lean_closure_set(v___f_272_, 3, v_x_264_);
v___x_273_ = lean_apply_1(v_f_262_, v_head_270_);
v___x_274_ = lean_apply_4(v_toBind_269_, lean_box(0), lean_box(0), v___x_273_, v___f_272_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0(lean_object* v_inst_275_, lean_object* v_f_276_, lean_object* v_tail_277_, lean_object* v_x_278_, lean_object* v_____do__lift_279_){
_start:
{
if (lean_obj_tag(v_____do__lift_279_) == 0)
{
lean_object* v___x_280_; 
v___x_280_ = l_List_filterMapM_loop___redArg(v_inst_275_, v_f_276_, v_tail_277_, v_x_278_);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_val_281_ = lean_ctor_get(v_____do__lift_279_, 0);
lean_inc(v_val_281_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v_val_281_);
lean_ctor_set(v___x_282_, 1, v_x_278_);
v___x_283_ = l_List_filterMapM_loop___redArg(v_inst_275_, v_f_276_, v_tail_277_, v___x_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop(lean_object* v_m_284_, lean_object* v_inst_285_, lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_f_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_List_filterMapM_loop___redArg(v_inst_285_, v_f_288_, v_x_289_, v_x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM___redArg(lean_object* v_inst_292_, lean_object* v_f_293_, lean_object* v_as_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
v___x_296_ = l_List_filterMapM_loop___redArg(v_inst_292_, v_f_293_, v_as_294_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM(lean_object* v_m_297_, lean_object* v_inst_298_, lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_f_301_, lean_object* v_as_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(0);
v___x_304_ = l_List_filterMapM_loop___redArg(v_inst_298_, v_f_301_, v_as_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___redArg(lean_object* v_inst_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_toApplicative_309_; lean_object* v_toPure_310_; lean_object* v___x_311_; 
v_toApplicative_309_ = lean_ctor_get(v_inst_305_, 0);
lean_inc_ref(v_toApplicative_309_);
lean_dec(v_x_306_);
lean_dec_ref(v_inst_305_);
v_toPure_310_ = lean_ctor_get(v_toApplicative_309_, 1);
lean_inc(v_toPure_310_);
lean_dec_ref(v_toApplicative_309_);
v___x_311_ = lean_apply_2(v_toPure_310_, lean_box(0), v_x_307_);
return v___x_311_;
}
else
{
lean_object* v_toBind_312_; lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_toBind_312_ = lean_ctor_get(v_inst_305_, 1);
lean_inc(v_toBind_312_);
v_head_313_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_head_313_);
v_tail_314_ = lean_ctor_get(v_x_308_, 1);
lean_inc(v_tail_314_);
lean_dec_ref_known(v_x_308_, 2);
lean_inc(v_x_306_);
v___f_315_ = lean_alloc_closure((void*)(l_List_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_315_, 0, v_inst_305_);
lean_closure_set(v___f_315_, 1, v_x_306_);
lean_closure_set(v___f_315_, 2, v_tail_314_);
v___x_316_ = lean_apply_2(v_x_306_, v_x_307_, v_head_313_);
v___x_317_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_316_, v___f_315_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___redArg___lam__0(lean_object* v_inst_318_, lean_object* v_x_319_, lean_object* v_tail_320_, lean_object* v_s_x27_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_List_foldlM___redArg(v_inst_318_, v_x_319_, v_s_x27_321_, v_tail_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM(lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_s_325_, lean_object* v_00_u03b1_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_List_foldlM___redArg(v_inst_324_, v_x_327_, v_x_328_, v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg___lam__0(lean_object* v_f_331_, lean_object* v_s_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_2(v_f_331_, v_a_333_, v_s_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg(lean_object* v_inst_335_, lean_object* v_f_336_, lean_object* v_init_337_, lean_object* v_l_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_339_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_339_, 0, v_f_336_);
v___x_340_ = l_List_reverse___redArg(v_l_338_);
v___x_341_ = l_List_foldlM___redArg(v_inst_335_, v___f_339_, v_init_337_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM(lean_object* v_m_342_, lean_object* v_inst_343_, lean_object* v_s_344_, lean_object* v_00_u03b1_345_, lean_object* v_f_346_, lean_object* v_init_347_, lean_object* v_l_348_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___f_349_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_349_, 0, v_f_346_);
v___x_350_ = l_List_reverse___redArg(v_l_348_);
v___x_351_ = l_List_foldlM___redArg(v_inst_343_, v___f_349_, v_init_347_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg(lean_object* v_inst_352_, lean_object* v_f_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v_failure_355_; lean_object* v___x_356_; 
lean_dec(v_f_353_);
v_failure_355_ = lean_ctor_get(v_inst_352_, 1);
lean_inc(v_failure_355_);
lean_dec_ref(v_inst_352_);
v___x_356_ = lean_apply_1(v_failure_355_, lean_box(0));
return v___x_356_;
}
else
{
lean_object* v_head_357_; lean_object* v_tail_358_; lean_object* v_orElse_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_head_357_ = lean_ctor_get(v_x_354_, 0);
lean_inc(v_head_357_);
v_tail_358_ = lean_ctor_get(v_x_354_, 1);
lean_inc(v_tail_358_);
lean_dec_ref_known(v_x_354_, 2);
v_orElse_359_ = lean_ctor_get(v_inst_352_, 2);
lean_inc(v_orElse_359_);
lean_inc(v_f_353_);
v___f_360_ = lean_alloc_closure((void*)(l_List_firstM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_360_, 0, v_inst_352_);
lean_closure_set(v___f_360_, 1, v_f_353_);
lean_closure_set(v___f_360_, 2, v_tail_358_);
v___x_361_ = lean_apply_1(v_f_353_, v_head_357_);
v___x_362_ = lean_apply_3(v_orElse_359_, lean_box(0), v___x_361_, v___f_360_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg___lam__0(lean_object* v_inst_363_, lean_object* v_f_364_, lean_object* v_tail_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_List_firstM___redArg(v_inst_363_, v_f_364_, v_tail_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_List_firstM(lean_object* v_m_368_, lean_object* v_inst_369_, lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_f_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_List_firstM___redArg(v_inst_369_, v_f_372_, v_x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0___boxed(lean_object* v_inst_375_, lean_object* v_p_376_, lean_object* v_tail_377_, lean_object* v_toPure_378_, lean_object* v_____do__lift_379_){
_start:
{
uint8_t v_____do__lift_73__boxed_380_; lean_object* v_res_381_; 
v_____do__lift_73__boxed_380_ = lean_unbox(v_____do__lift_379_);
v_res_381_ = l_List_anyM___redArg___lam__0(v_inst_375_, v_p_376_, v_tail_377_, v_toPure_378_, v_____do__lift_73__boxed_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg(lean_object* v_inst_382_, lean_object* v_p_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v_toApplicative_385_; lean_object* v_toPure_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_toApplicative_385_ = lean_ctor_get(v_inst_382_, 0);
lean_inc_ref(v_toApplicative_385_);
lean_dec(v_p_383_);
lean_dec_ref(v_inst_382_);
v_toPure_386_ = lean_ctor_get(v_toApplicative_385_, 1);
lean_inc(v_toPure_386_);
lean_dec_ref(v_toApplicative_385_);
v___x_387_ = 0;
v___x_388_ = lean_box(v___x_387_);
v___x_389_ = lean_apply_2(v_toPure_386_, lean_box(0), v___x_388_);
return v___x_389_;
}
else
{
lean_object* v_toApplicative_390_; lean_object* v_toBind_391_; lean_object* v_toPure_392_; lean_object* v_head_393_; lean_object* v_tail_394_; lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_toApplicative_390_ = lean_ctor_get(v_inst_382_, 0);
v_toBind_391_ = lean_ctor_get(v_inst_382_, 1);
lean_inc(v_toBind_391_);
v_toPure_392_ = lean_ctor_get(v_toApplicative_390_, 1);
lean_inc(v_toPure_392_);
v_head_393_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_393_);
v_tail_394_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_tail_394_);
lean_dec_ref_known(v_x_384_, 2);
lean_inc(v_p_383_);
v___f_395_ = lean_alloc_closure((void*)(l_List_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_395_, 0, v_inst_382_);
lean_closure_set(v___f_395_, 1, v_p_383_);
lean_closure_set(v___f_395_, 2, v_tail_394_);
lean_closure_set(v___f_395_, 3, v_toPure_392_);
v___x_396_ = lean_apply_1(v_p_383_, v_head_393_);
v___x_397_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v___x_396_, v___f_395_);
return v___x_397_;
}
}
}
lean_object* l_List_anyM___redArg___lam__0(lean_object* v_inst_398_, lean_object* v_p_399_, lean_object* v_tail_400_, lean_object* v_toPure_401_, uint8_t v_____do__lift_402_){
_start:
{
if (v_____do__lift_402_ == 0)
{
lean_object* v___x_403_; 
lean_dec(v_toPure_401_);
v___x_403_ = l_List_anyM___redArg(v_inst_398_, v_p_399_, v_tail_400_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_tail_400_);
lean_dec(v_p_399_);
lean_dec_ref(v_inst_398_);
v___x_404_ = lean_box(v_____do__lift_402_);
v___x_405_ = lean_apply_2(v_toPure_401_, lean_box(0), v___x_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT void l_List_anyM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_398_ = stack[0].m_obj;
lean_object* v_p_399_ = stack[1].m_obj;
lean_object* v_tail_400_ = stack[2].m_obj;
lean_object* v_toPure_401_ = stack[3].m_obj;
uint8_t v_____do__lift_402_ = stack[4].m_num;
lean_object* v_res_406_;
v_res_406_ = l_List_anyM___redArg___lam__0(v_inst_398_, v_p_399_, v_tail_400_, v_toPure_401_, v_____do__lift_402_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_List_anyM(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_00_u03b1_409_, lean_object* v_p_410_, lean_object* v_x_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_List_anyM___redArg(v_inst_408_, v_p_410_, v_x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0___boxed(lean_object* v_toPure_413_, lean_object* v_inst_414_, lean_object* v_p_415_, lean_object* v_tail_416_, lean_object* v_____do__lift_417_){
_start:
{
uint8_t v_____do__lift_73__boxed_418_; lean_object* v_res_419_; 
v_____do__lift_73__boxed_418_ = lean_unbox(v_____do__lift_417_);
v_res_419_ = l_List_allM___redArg___lam__0(v_toPure_413_, v_inst_414_, v_p_415_, v_tail_416_, v_____do__lift_73__boxed_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg(lean_object* v_inst_420_, lean_object* v_p_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v_toApplicative_423_; lean_object* v_toPure_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_toApplicative_423_ = lean_ctor_get(v_inst_420_, 0);
lean_inc_ref(v_toApplicative_423_);
lean_dec(v_p_421_);
lean_dec_ref(v_inst_420_);
v_toPure_424_ = lean_ctor_get(v_toApplicative_423_, 1);
lean_inc(v_toPure_424_);
lean_dec_ref(v_toApplicative_423_);
v___x_425_ = 1;
v___x_426_ = lean_box(v___x_425_);
v___x_427_ = lean_apply_2(v_toPure_424_, lean_box(0), v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_toApplicative_428_; lean_object* v_toBind_429_; lean_object* v_toPure_430_; lean_object* v_head_431_; lean_object* v_tail_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_toApplicative_428_ = lean_ctor_get(v_inst_420_, 0);
v_toBind_429_ = lean_ctor_get(v_inst_420_, 1);
lean_inc(v_toBind_429_);
v_toPure_430_ = lean_ctor_get(v_toApplicative_428_, 1);
lean_inc(v_toPure_430_);
v_head_431_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_head_431_);
v_tail_432_ = lean_ctor_get(v_x_422_, 1);
lean_inc(v_tail_432_);
lean_dec_ref_known(v_x_422_, 2);
lean_inc(v_p_421_);
v___f_433_ = lean_alloc_closure((void*)(l_List_allM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_433_, 0, v_toPure_430_);
lean_closure_set(v___f_433_, 1, v_inst_420_);
lean_closure_set(v___f_433_, 2, v_p_421_);
lean_closure_set(v___f_433_, 3, v_tail_432_);
v___x_434_ = lean_apply_1(v_p_421_, v_head_431_);
v___x_435_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_434_, v___f_433_);
return v___x_435_;
}
}
}
lean_object* l_List_allM___redArg___lam__0(lean_object* v_toPure_436_, lean_object* v_inst_437_, lean_object* v_p_438_, lean_object* v_tail_439_, uint8_t v_____do__lift_440_){
_start:
{
if (v_____do__lift_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_tail_439_);
lean_dec(v_p_438_);
lean_dec_ref(v_inst_437_);
v___x_441_ = lean_box(v_____do__lift_440_);
v___x_442_ = lean_apply_2(v_toPure_436_, lean_box(0), v___x_441_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v_toPure_436_);
v___x_443_ = l_List_allM___redArg(v_inst_437_, v_p_438_, v_tail_439_);
return v___x_443_;
}
}
}
LEAN_EXPORT void l_List_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_436_ = stack[0].m_obj;
lean_object* v_inst_437_ = stack[1].m_obj;
lean_object* v_p_438_ = stack[2].m_obj;
lean_object* v_tail_439_ = stack[3].m_obj;
uint8_t v_____do__lift_440_ = stack[4].m_num;
lean_object* v_res_444_;
v_res_444_ = l_List_allM___redArg___lam__0(v_toPure_436_, v_inst_437_, v_p_438_, v_tail_439_, v_____do__lift_440_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_List_allM(lean_object* v_m_445_, lean_object* v_inst_446_, lean_object* v_00_u03b1_447_, lean_object* v_p_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_List_allM___redArg(v_inst_446_, v_p_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0___boxed(lean_object* v_inst_451_, lean_object* v_p_452_, lean_object* v_tail_453_, lean_object* v_head_454_, lean_object* v_toPure_455_, lean_object* v_____do__lift_456_){
_start:
{
uint8_t v_____do__lift_76__boxed_457_; lean_object* v_res_458_; 
v_____do__lift_76__boxed_457_ = lean_unbox(v_____do__lift_456_);
v_res_458_ = l_List_findM_x3f___redArg___lam__0(v_inst_451_, v_p_452_, v_tail_453_, v_head_454_, v_toPure_455_, v_____do__lift_76__boxed_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg(lean_object* v_inst_459_, lean_object* v_p_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v_toApplicative_462_; lean_object* v_toPure_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_459_, 0);
lean_inc_ref(v_toApplicative_462_);
lean_dec(v_p_460_);
lean_dec_ref(v_inst_459_);
v_toPure_463_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_463_);
lean_dec_ref(v_toApplicative_462_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_apply_2(v_toPure_463_, lean_box(0), v___x_464_);
return v___x_465_;
}
else
{
lean_object* v_toApplicative_466_; lean_object* v_toBind_467_; lean_object* v_toPure_468_; lean_object* v_head_469_; lean_object* v_tail_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_toApplicative_466_ = lean_ctor_get(v_inst_459_, 0);
v_toBind_467_ = lean_ctor_get(v_inst_459_, 1);
lean_inc(v_toBind_467_);
v_toPure_468_ = lean_ctor_get(v_toApplicative_466_, 1);
lean_inc(v_toPure_468_);
v_head_469_ = lean_ctor_get(v_x_461_, 0);
lean_inc_n(v_head_469_, 2);
v_tail_470_ = lean_ctor_get(v_x_461_, 1);
lean_inc(v_tail_470_);
lean_dec_ref_known(v_x_461_, 2);
lean_inc(v_p_460_);
v___f_471_ = lean_alloc_closure((void*)(l_List_findM_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_471_, 0, v_inst_459_);
lean_closure_set(v___f_471_, 1, v_p_460_);
lean_closure_set(v___f_471_, 2, v_tail_470_);
lean_closure_set(v___f_471_, 3, v_head_469_);
lean_closure_set(v___f_471_, 4, v_toPure_468_);
v___x_472_ = lean_apply_1(v_p_460_, v_head_469_);
v___x_473_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_472_, v___f_471_);
return v___x_473_;
}
}
}
lean_object* l_List_findM_x3f___redArg___lam__0(lean_object* v_inst_474_, lean_object* v_p_475_, lean_object* v_tail_476_, lean_object* v_head_477_, lean_object* v_toPure_478_, uint8_t v_____do__lift_479_){
_start:
{
if (v_____do__lift_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec(v_toPure_478_);
lean_dec(v_head_477_);
v___x_480_ = l_List_findM_x3f___redArg(v_inst_474_, v_p_475_, v_tail_476_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_tail_476_);
lean_dec(v_p_475_);
lean_dec_ref(v_inst_474_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v_head_477_);
v___x_482_ = lean_apply_2(v_toPure_478_, lean_box(0), v___x_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT void l_List_findM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_474_ = stack[0].m_obj;
lean_object* v_p_475_ = stack[1].m_obj;
lean_object* v_tail_476_ = stack[2].m_obj;
lean_object* v_head_477_ = stack[3].m_obj;
lean_object* v_toPure_478_ = stack[4].m_obj;
uint8_t v_____do__lift_479_ = stack[5].m_num;
lean_object* v_res_483_;
v_res_483_ = l_List_findM_x3f___redArg___lam__0(v_inst_474_, v_p_475_, v_tail_476_, v_head_477_, v_toPure_478_, v_____do__lift_479_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_List_findM_x3f(lean_object* v_m_484_, lean_object* v_inst_485_, lean_object* v_00_u03b1_486_, lean_object* v_p_487_, lean_object* v_x_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_List_findM_x3f___redArg(v_inst_485_, v_p_487_, v_x_488_);
return v___x_489_;
}
}
lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (v_____do__lift_490_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v_h__1_491_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_apply_1(v_h__2_492_, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_h__2_492_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_1(v_h__1_491_, v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_490_ = stack[0].m_num;
lean_object* v_h__1_491_ = stack[1].m_obj;
lean_object* v_h__2_492_ = stack[2].m_obj;
lean_object* v_res_497_;
v_res_497_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_490_, v_h__1_491_, v_h__2_492_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
uint8_t v_____do__lift_24__boxed_501_; lean_object* v_res_502_; 
v_____do__lift_24__boxed_501_ = lean_unbox(v_____do__lift_498_);
v_res_502_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_501_, v_h__1_499_, v_h__2_500_);
return v_res_502_;
}
}
lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_object* v_motive_503_, uint8_t v_____do__lift_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
if (v_____do__lift_504_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_505_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__2_506_, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__1_505_, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_504_ = stack[1].m_num;
lean_object* v_h__1_505_ = stack[2].m_obj;
lean_object* v_h__2_506_ = stack[3].m_obj;
lean_object* v_res_511_;
v_res_511_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_box(0), v_____do__lift_504_, v_h__1_505_, v_h__2_506_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_512_, lean_object* v_____do__lift_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
uint8_t v_____do__lift_41__boxed_516_; lean_object* v_res_517_; 
v_____do__lift_41__boxed_516_ = lean_unbox(v_____do__lift_513_);
v_res_517_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(v_motive_512_, v_____do__lift_41__boxed_516_, v_h__1_514_, v_h__2_515_);
return v_res_517_;
}
}
lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(uint8_t v_x_518_, lean_object* v_h__1_519_, lean_object* v_h__2_520_){
_start:
{
if (v_x_518_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_h__1_519_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_1(v_h__2_520_, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v_h__2_520_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_apply_1(v_h__1_519_, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_518_ = stack[0].m_num;
lean_object* v_h__1_519_ = stack[1].m_obj;
lean_object* v_h__2_520_ = stack[2].m_obj;
lean_object* v_res_525_;
v_res_525_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_518_, v_h__1_519_, v_h__2_520_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
uint8_t v_x_24__boxed_529_; lean_object* v_res_530_; 
v_x_24__boxed_529_ = lean_unbox(v_x_526_);
v_res_530_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_529_, v_h__1_527_, v_h__2_528_);
return v_res_530_;
}
}
lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_object* v_motive_531_, uint8_t v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (v_x_532_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_h__1_533_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v_h__2_534_, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_534_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__1_533_, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Control_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_532_ = stack[1].m_num;
lean_object* v_h__1_533_ = stack[2].m_obj;
lean_object* v_h__2_534_ = stack[3].m_obj;
lean_object* v_res_539_;
v_res_539_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_box(0), v_x_532_, v_h__1_533_, v_h__2_534_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_540_, lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
uint8_t v_x_41__boxed_544_; lean_object* v_res_545_; 
v_x_41__boxed_544_ = lean_unbox(v_x_541_);
v_res_545_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(v_motive_540_, v_x_41__boxed_544_, v_h__1_542_, v_h__2_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg(lean_object* v_inst_546_, lean_object* v_f_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_object* v_toApplicative_549_; lean_object* v_toPure_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toApplicative_549_ = lean_ctor_get(v_inst_546_, 0);
lean_inc_ref(v_toApplicative_549_);
lean_dec(v_f_547_);
lean_dec_ref(v_inst_546_);
v_toPure_550_ = lean_ctor_get(v_toApplicative_549_, 1);
lean_inc(v_toPure_550_);
lean_dec_ref(v_toApplicative_549_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_2(v_toPure_550_, lean_box(0), v___x_551_);
return v___x_552_;
}
else
{
lean_object* v_toApplicative_553_; lean_object* v_toBind_554_; lean_object* v_toPure_555_; lean_object* v_head_556_; lean_object* v_tail_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_toApplicative_553_ = lean_ctor_get(v_inst_546_, 0);
v_toBind_554_ = lean_ctor_get(v_inst_546_, 1);
lean_inc(v_toBind_554_);
v_toPure_555_ = lean_ctor_get(v_toApplicative_553_, 1);
lean_inc(v_toPure_555_);
v_head_556_ = lean_ctor_get(v_x_548_, 0);
lean_inc(v_head_556_);
v_tail_557_ = lean_ctor_get(v_x_548_, 1);
lean_inc(v_tail_557_);
lean_dec_ref_known(v_x_548_, 2);
lean_inc(v_f_547_);
v___f_558_ = lean_alloc_closure((void*)(l_List_findSomeM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_558_, 0, v_inst_546_);
lean_closure_set(v___f_558_, 1, v_f_547_);
lean_closure_set(v___f_558_, 2, v_tail_557_);
lean_closure_set(v___f_558_, 3, v_toPure_555_);
v___x_559_ = lean_apply_1(v_f_547_, v_head_556_);
v___x_560_ = lean_apply_4(v_toBind_554_, lean_box(0), lean_box(0), v___x_559_, v___f_558_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg___lam__0(lean_object* v_inst_561_, lean_object* v_f_562_, lean_object* v_tail_563_, lean_object* v_toPure_564_, lean_object* v_____do__lift_565_){
_start:
{
if (lean_obj_tag(v_____do__lift_565_) == 0)
{
lean_object* v___x_566_; 
lean_dec(v_toPure_564_);
v___x_566_ = l_List_findSomeM_x3f___redArg(v_inst_561_, v_f_562_, v_tail_563_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
lean_dec(v_tail_563_);
lean_dec(v_f_562_);
lean_dec_ref(v_inst_561_);
v___x_567_ = lean_apply_2(v_toPure_564_, lean_box(0), v_____do__lift_565_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f(lean_object* v_m_568_, lean_object* v_inst_569_, lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_f_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_List_findSomeM_x3f___redArg(v_inst_569_, v_f_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
if (lean_obj_tag(v_____do__lift_575_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__1_576_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_h__2_577_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v_val_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_577_);
v_val_580_ = lean_ctor_get(v_____do__lift_575_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v_____do__lift_575_, 1);
v___x_581_ = lean_apply_1(v_h__1_576_, v_val_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_582_, lean_object* v_motive_583_, lean_object* v_____do__lift_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
if (lean_obj_tag(v_____do__lift_584_) == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__1_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__2_586_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; 
lean_dec(v_h__2_586_);
v_val_589_ = lean_ctor_get(v_____do__lift_584_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_____do__lift_584_, 1);
v___x_590_ = lean_apply_1(v_h__1_585_, v_val_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_591_, lean_object* v_h__1_592_, lean_object* v_h__2_593_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_h__1_592_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_apply_1(v_h__2_593_, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_597_; 
lean_dec(v_h__2_593_);
v_val_596_ = lean_ctor_get(v_x_591_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_x_591_, 1);
v___x_597_ = lean_apply_1(v_h__1_592_, v_val_596_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_598_, lean_object* v_motive_599_, lean_object* v_x_600_, lean_object* v_h__1_601_, lean_object* v_h__2_602_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_h__1_601_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_apply_1(v_h__2_602_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_606_; 
lean_dec(v_h__2_602_);
v_val_605_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_x_600_, 1);
v___x_606_ = lean_apply_1(v_h__1_601_, v_val_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_607_, lean_object* v_inst_608_, lean_object* v_f_609_, lean_object* v_tail_610_, lean_object* v_____do__lift_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_List_forIn_x27_loop___redArg___lam__0(v_toPure_607_, v_inst_608_, v_f_609_, v_tail_610_, v_____do__lift_611_);
lean_dec(v_tail_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object* v_inst_613_, lean_object* v_f_614_, lean_object* v_as_x27_615_, lean_object* v_b_616_){
_start:
{
if (lean_obj_tag(v_as_x27_615_) == 0)
{
lean_object* v_toApplicative_617_; lean_object* v_toPure_618_; lean_object* v___x_619_; 
v_toApplicative_617_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_ref(v_toApplicative_617_);
lean_dec(v_f_614_);
lean_dec_ref(v_inst_613_);
v_toPure_618_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_inc(v_toPure_618_);
lean_dec_ref(v_toApplicative_617_);
v___x_619_ = lean_apply_2(v_toPure_618_, lean_box(0), v_b_616_);
return v___x_619_;
}
else
{
lean_object* v_toApplicative_620_; lean_object* v_toBind_621_; lean_object* v_toPure_622_; lean_object* v_head_623_; lean_object* v_tail_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_toApplicative_620_ = lean_ctor_get(v_inst_613_, 0);
v_toBind_621_ = lean_ctor_get(v_inst_613_, 1);
lean_inc(v_toBind_621_);
v_toPure_622_ = lean_ctor_get(v_toApplicative_620_, 1);
lean_inc(v_toPure_622_);
v_head_623_ = lean_ctor_get(v_as_x27_615_, 0);
v_tail_624_ = lean_ctor_get(v_as_x27_615_, 1);
lean_inc(v_tail_624_);
lean_inc(v_f_614_);
v___f_625_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_625_, 0, v_toPure_622_);
lean_closure_set(v___f_625_, 1, v_inst_613_);
lean_closure_set(v___f_625_, 2, v_f_614_);
lean_closure_set(v___f_625_, 3, v_tail_624_);
lean_inc(v_head_623_);
v___x_626_ = lean_apply_3(v_f_614_, v_head_623_, lean_box(0), v_b_616_);
v___x_627_ = lean_apply_4(v_toBind_621_, lean_box(0), lean_box(0), v___x_626_, v___f_625_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_628_, lean_object* v_inst_629_, lean_object* v_f_630_, lean_object* v_tail_631_, lean_object* v_____do__lift_632_){
_start:
{
if (lean_obj_tag(v_____do__lift_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
lean_dec(v_f_630_);
lean_dec_ref(v_inst_629_);
v_a_633_ = lean_ctor_get(v_____do__lift_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v_____do__lift_632_, 1);
v___x_634_ = lean_apply_2(v_toPure_628_, lean_box(0), v_a_633_);
return v___x_634_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_636_; 
lean_dec(v_toPure_628_);
v_a_635_ = lean_ctor_get(v_____do__lift_632_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_____do__lift_632_, 1);
v___x_636_ = l_List_forIn_x27_loop___redArg(v_inst_629_, v_f_630_, v_tail_631_, v_a_635_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___boxed(lean_object* v_inst_637_, lean_object* v_f_638_, lean_object* v_as_x27_639_, lean_object* v_b_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_List_forIn_x27_loop___redArg(v_inst_637_, v_f_638_, v_as_x27_639_, v_b_640_);
lean_dec(v_as_x27_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_inst_645_, lean_object* v_as_646_, lean_object* v_f_647_, lean_object* v_as_x27_648_, lean_object* v_b_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_List_forIn_x27_loop___redArg(v_inst_645_, v_f_647_, v_as_x27_648_, v_b_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_m_654_, lean_object* v_inst_655_, lean_object* v_as_656_, lean_object* v_f_657_, lean_object* v_as_x27_658_, lean_object* v_b_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_List_forIn_x27_loop(v_00_u03b1_652_, v_00_u03b2_653_, v_m_654_, v_inst_655_, v_as_656_, v_f_657_, v_as_x27_658_, v_b_659_, v_a_660_);
lean_dec(v_as_x27_658_);
lean_dec(v_as_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object* v_inst_662_, lean_object* v_as_663_, lean_object* v_init_664_, lean_object* v_f_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_List_forIn_x27_loop___redArg(v_inst_662_, v_f_665_, v_as_663_, v_init_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg___boxed(lean_object* v_inst_667_, lean_object* v_as_668_, lean_object* v_init_669_, lean_object* v_f_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_List_forIn_x27___redArg(v_inst_667_, v_as_668_, v_init_669_, v_f_670_);
lean_dec(v_as_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_m_674_, lean_object* v_inst_675_, lean_object* v_as_676_, lean_object* v_init_677_, lean_object* v_f_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_List_forIn_x27_loop___redArg(v_inst_675_, v_f_678_, v_as_676_, v_init_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___boxed(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_m_682_, lean_object* v_inst_683_, lean_object* v_as_684_, lean_object* v_init_685_, lean_object* v_f_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_List_forIn_x27(v_00_u03b1_680_, v_00_u03b2_681_, v_m_682_, v_inst_683_, v_as_684_, v_init_685_, v_f_686_);
lean_dec(v_as_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_688_, lean_object* v_00_u03b2_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_List_forIn_x27_loop___redArg(v_inst_688_, v___y_692_, v___y_690_, v___y_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object* v_inst_694_, lean_object* v_00_u03b2_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(v_inst_694_, v_00_u03b2_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_700_){
_start:
{
lean_object* v___f_701_; 
v___f_701_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_701_, 0, v_inst_700_);
return v___f_701_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_702_, lean_object* v_00_u03b1_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v___f_705_; 
v___f_705_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_705_, 0, v_inst_704_);
return v___f_705_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad___redArg(lean_object* v_inst_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_707_, 0, lean_box(0));
lean_closure_set(v___x_707_, 1, v_inst_706_);
lean_closure_set(v___x_707_, 2, lean_box(0));
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad(lean_object* v_m_708_, lean_object* v_00_u03b1_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_711_, 0, lean_box(0));
lean_closure_set(v___x_711_, 1, v_inst_710_);
lean_closure_set(v___x_711_, 2, lean_box(0));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_List_instFunctor___lam__0(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_716_, 0, lean_box(0));
lean_closure_set(v___x_716_, 1, lean_box(0));
lean_closure_set(v___x_716_, 2, v___y_714_);
v___x_717_ = lean_box(0);
v___x_718_ = l_List_mapTR_loop___redArg(v___x_716_, v___y_715_, v___x_717_);
return v___x_718_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Control(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Control(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Control(builtin);
}
#ifdef __cplusplus
}
#endif
