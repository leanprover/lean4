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
LEAN_EXPORT lean_object* l_List_filterAuxM___redArg___lam__0(lean_object* v_inst_198_, lean_object* v_f_199_, lean_object* v_tail_200_, lean_object* v_x_201_, lean_object* v_head_202_, uint8_t v_b_203_){
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
LEAN_EXPORT lean_object* l_List_filterAuxM(lean_object* v_m_207_, lean_object* v_inst_208_, lean_object* v_00_u03b1_209_, lean_object* v_f_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_List_filterAuxM___redArg(v_inst_208_, v_f_210_, v_x_211_, v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_List_filterM___redArg___lam__0(lean_object* v_toPure_214_, lean_object* v_as_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_List_reverse___redArg(v_as_215_);
v___x_217_ = lean_apply_2(v_toPure_214_, lean_box(0), v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_List_filterM___redArg(lean_object* v_inst_218_, lean_object* v_p_219_, lean_object* v_as_220_){
_start:
{
lean_object* v_toApplicative_221_; lean_object* v_toBind_222_; lean_object* v_toPure_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___x_227_; 
v_toApplicative_221_ = lean_ctor_get(v_inst_218_, 0);
v_toBind_222_ = lean_ctor_get(v_inst_218_, 1);
lean_inc(v_toBind_222_);
v_toPure_223_ = lean_ctor_get(v_toApplicative_221_, 1);
lean_inc(v_toPure_223_);
v___x_224_ = lean_box(0);
v___x_225_ = l_List_filterAuxM___redArg(v_inst_218_, v_p_219_, v_as_220_, v___x_224_);
v___f_226_ = lean_alloc_closure((void*)(l_List_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_226_, 0, v_toPure_223_);
v___x_227_ = lean_apply_4(v_toBind_222_, lean_box(0), lean_box(0), v___x_225_, v___f_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_List_filterM(lean_object* v_m_228_, lean_object* v_inst_229_, lean_object* v_00_u03b1_230_, lean_object* v_p_231_, lean_object* v_as_232_){
_start:
{
lean_object* v_toApplicative_233_; lean_object* v_toBind_234_; lean_object* v_toPure_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; 
v_toApplicative_233_ = lean_ctor_get(v_inst_229_, 0);
v_toBind_234_ = lean_ctor_get(v_inst_229_, 1);
lean_inc(v_toBind_234_);
v_toPure_235_ = lean_ctor_get(v_toApplicative_233_, 1);
lean_inc(v_toPure_235_);
v___x_236_ = lean_box(0);
v___x_237_ = l_List_filterAuxM___redArg(v_inst_229_, v_p_231_, v_as_232_, v___x_236_);
v___f_238_ = lean_alloc_closure((void*)(l_List_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_toPure_235_);
v___x_239_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_237_, v___f_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_List_filterRevM___redArg(lean_object* v_inst_240_, lean_object* v_p_241_, lean_object* v_as_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = l_List_reverse___redArg(v_as_242_);
v___x_244_ = lean_box(0);
v___x_245_ = l_List_filterAuxM___redArg(v_inst_240_, v_p_241_, v___x_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_List_filterRevM(lean_object* v_m_246_, lean_object* v_inst_247_, lean_object* v_00_u03b1_248_, lean_object* v_p_249_, lean_object* v_as_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_List_reverse___redArg(v_as_250_);
v___x_252_ = lean_box(0);
v___x_253_ = l_List_filterAuxM___redArg(v_inst_247_, v_p_249_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0___boxed(lean_object* v_inst_254_, lean_object* v_f_255_, lean_object* v_tail_256_, lean_object* v_x_257_, lean_object* v_____do__lift_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_List_filterMapM_loop___redArg___lam__0(v_inst_254_, v_f_255_, v_tail_256_, v_x_257_, v_____do__lift_258_);
lean_dec(v_____do__lift_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg(lean_object* v_inst_260_, lean_object* v_f_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v_toApplicative_264_; lean_object* v_toPure_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_toApplicative_264_ = lean_ctor_get(v_inst_260_, 0);
lean_inc_ref(v_toApplicative_264_);
lean_dec(v_f_261_);
lean_dec_ref(v_inst_260_);
v_toPure_265_ = lean_ctor_get(v_toApplicative_264_, 1);
lean_inc(v_toPure_265_);
lean_dec_ref(v_toApplicative_264_);
v___x_266_ = l_List_reverse___redArg(v_x_263_);
v___x_267_ = lean_apply_2(v_toPure_265_, lean_box(0), v___x_266_);
return v___x_267_;
}
else
{
lean_object* v_toBind_268_; lean_object* v_head_269_; lean_object* v_tail_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_toBind_268_ = lean_ctor_get(v_inst_260_, 1);
lean_inc(v_toBind_268_);
v_head_269_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_head_269_);
v_tail_270_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_tail_270_);
lean_dec_ref_known(v_x_262_, 2);
lean_inc(v_f_261_);
v___f_271_ = lean_alloc_closure((void*)(l_List_filterMapM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_271_, 0, v_inst_260_);
lean_closure_set(v___f_271_, 1, v_f_261_);
lean_closure_set(v___f_271_, 2, v_tail_270_);
lean_closure_set(v___f_271_, 3, v_x_263_);
v___x_272_ = lean_apply_1(v_f_261_, v_head_269_);
v___x_273_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_272_, v___f_271_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___redArg___lam__0(lean_object* v_inst_274_, lean_object* v_f_275_, lean_object* v_tail_276_, lean_object* v_x_277_, lean_object* v_____do__lift_278_){
_start:
{
if (lean_obj_tag(v_____do__lift_278_) == 0)
{
lean_object* v___x_279_; 
v___x_279_ = l_List_filterMapM_loop___redArg(v_inst_274_, v_f_275_, v_tail_276_, v_x_277_);
return v___x_279_;
}
else
{
lean_object* v_val_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_val_280_ = lean_ctor_get(v_____do__lift_278_, 0);
lean_inc(v_val_280_);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v_val_280_);
lean_ctor_set(v___x_281_, 1, v_x_277_);
v___x_282_ = l_List_filterMapM_loop___redArg(v_inst_274_, v_f_275_, v_tail_276_, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop(lean_object* v_m_283_, lean_object* v_inst_284_, lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_f_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_List_filterMapM_loop___redArg(v_inst_284_, v_f_287_, v_x_288_, v_x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM___redArg(lean_object* v_inst_291_, lean_object* v_f_292_, lean_object* v_as_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = l_List_filterMapM_loop___redArg(v_inst_291_, v_f_292_, v_as_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM(lean_object* v_m_296_, lean_object* v_inst_297_, lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_f_300_, lean_object* v_as_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(0);
v___x_303_ = l_List_filterMapM_loop___redArg(v_inst_297_, v_f_300_, v_as_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___redArg(lean_object* v_inst_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_toApplicative_308_; lean_object* v_toPure_309_; lean_object* v___x_310_; 
v_toApplicative_308_ = lean_ctor_get(v_inst_304_, 0);
lean_inc_ref(v_toApplicative_308_);
lean_dec(v_x_305_);
lean_dec_ref(v_inst_304_);
v_toPure_309_ = lean_ctor_get(v_toApplicative_308_, 1);
lean_inc(v_toPure_309_);
lean_dec_ref(v_toApplicative_308_);
v___x_310_ = lean_apply_2(v_toPure_309_, lean_box(0), v_x_306_);
return v___x_310_;
}
else
{
lean_object* v_toBind_311_; lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v___f_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_toBind_311_ = lean_ctor_get(v_inst_304_, 1);
lean_inc(v_toBind_311_);
v_head_312_ = lean_ctor_get(v_x_307_, 0);
lean_inc(v_head_312_);
v_tail_313_ = lean_ctor_get(v_x_307_, 1);
lean_inc(v_tail_313_);
lean_dec_ref_known(v_x_307_, 2);
lean_inc(v_x_305_);
v___f_314_ = lean_alloc_closure((void*)(l_List_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_314_, 0, v_inst_304_);
lean_closure_set(v___f_314_, 1, v_x_305_);
lean_closure_set(v___f_314_, 2, v_tail_313_);
v___x_315_ = lean_apply_2(v_x_305_, v_x_306_, v_head_312_);
v___x_316_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_315_, v___f_314_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___redArg___lam__0(lean_object* v_inst_317_, lean_object* v_x_318_, lean_object* v_tail_319_, lean_object* v_s_x27_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_List_foldlM___redArg(v_inst_317_, v_x_318_, v_s_x27_320_, v_tail_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM(lean_object* v_m_322_, lean_object* v_inst_323_, lean_object* v_s_324_, lean_object* v_00_u03b1_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_List_foldlM___redArg(v_inst_323_, v_x_326_, v_x_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg___lam__0(lean_object* v_f_330_, lean_object* v_s_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_apply_2(v_f_330_, v_a_332_, v_s_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg(lean_object* v_inst_334_, lean_object* v_f_335_, lean_object* v_init_336_, lean_object* v_l_337_){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___f_338_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_338_, 0, v_f_335_);
v___x_339_ = l_List_reverse___redArg(v_l_337_);
v___x_340_ = l_List_foldlM___redArg(v_inst_334_, v___f_338_, v_init_336_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM(lean_object* v_m_341_, lean_object* v_inst_342_, lean_object* v_s_343_, lean_object* v_00_u03b1_344_, lean_object* v_f_345_, lean_object* v_init_346_, lean_object* v_l_347_){
_start:
{
lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___f_348_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_348_, 0, v_f_345_);
v___x_349_ = l_List_reverse___redArg(v_l_347_);
v___x_350_ = l_List_foldlM___redArg(v_inst_342_, v___f_348_, v_init_346_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg(lean_object* v_inst_351_, lean_object* v_f_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
lean_object* v_failure_354_; lean_object* v___x_355_; 
lean_dec(v_f_352_);
v_failure_354_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_failure_354_);
lean_dec_ref(v_inst_351_);
v___x_355_ = lean_apply_1(v_failure_354_, lean_box(0));
return v___x_355_;
}
else
{
lean_object* v_head_356_; lean_object* v_tail_357_; lean_object* v_orElse_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_head_356_ = lean_ctor_get(v_x_353_, 0);
lean_inc(v_head_356_);
v_tail_357_ = lean_ctor_get(v_x_353_, 1);
lean_inc(v_tail_357_);
lean_dec_ref_known(v_x_353_, 2);
v_orElse_358_ = lean_ctor_get(v_inst_351_, 2);
lean_inc(v_orElse_358_);
lean_inc(v_f_352_);
v___f_359_ = lean_alloc_closure((void*)(l_List_firstM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_359_, 0, v_inst_351_);
lean_closure_set(v___f_359_, 1, v_f_352_);
lean_closure_set(v___f_359_, 2, v_tail_357_);
v___x_360_ = lean_apply_1(v_f_352_, v_head_356_);
v___x_361_ = lean_apply_3(v_orElse_358_, lean_box(0), v___x_360_, v___f_359_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg___lam__0(lean_object* v_inst_362_, lean_object* v_f_363_, lean_object* v_tail_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_firstM___redArg(v_inst_362_, v_f_363_, v_tail_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_List_firstM(lean_object* v_m_367_, lean_object* v_inst_368_, lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_f_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_List_firstM___redArg(v_inst_368_, v_f_371_, v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0___boxed(lean_object* v_inst_374_, lean_object* v_p_375_, lean_object* v_tail_376_, lean_object* v_toPure_377_, lean_object* v_____do__lift_378_){
_start:
{
uint8_t v_____do__lift_73__boxed_379_; lean_object* v_res_380_; 
v_____do__lift_73__boxed_379_ = lean_unbox(v_____do__lift_378_);
v_res_380_ = l_List_anyM___redArg___lam__0(v_inst_374_, v_p_375_, v_tail_376_, v_toPure_377_, v_____do__lift_73__boxed_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg(lean_object* v_inst_381_, lean_object* v_p_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v_toApplicative_384_; lean_object* v_toPure_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_toApplicative_384_ = lean_ctor_get(v_inst_381_, 0);
lean_inc_ref(v_toApplicative_384_);
lean_dec(v_p_382_);
lean_dec_ref(v_inst_381_);
v_toPure_385_ = lean_ctor_get(v_toApplicative_384_, 1);
lean_inc(v_toPure_385_);
lean_dec_ref(v_toApplicative_384_);
v___x_386_ = 0;
v___x_387_ = lean_box(v___x_386_);
v___x_388_ = lean_apply_2(v_toPure_385_, lean_box(0), v___x_387_);
return v___x_388_;
}
else
{
lean_object* v_toApplicative_389_; lean_object* v_toBind_390_; lean_object* v_toPure_391_; lean_object* v_head_392_; lean_object* v_tail_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_toApplicative_389_ = lean_ctor_get(v_inst_381_, 0);
v_toBind_390_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_toBind_390_);
v_toPure_391_ = lean_ctor_get(v_toApplicative_389_, 1);
lean_inc(v_toPure_391_);
v_head_392_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_head_392_);
v_tail_393_ = lean_ctor_get(v_x_383_, 1);
lean_inc(v_tail_393_);
lean_dec_ref_known(v_x_383_, 2);
lean_inc(v_p_382_);
v___f_394_ = lean_alloc_closure((void*)(l_List_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_394_, 0, v_inst_381_);
lean_closure_set(v___f_394_, 1, v_p_382_);
lean_closure_set(v___f_394_, 2, v_tail_393_);
lean_closure_set(v___f_394_, 3, v_toPure_391_);
v___x_395_ = lean_apply_1(v_p_382_, v_head_392_);
v___x_396_ = lean_apply_4(v_toBind_390_, lean_box(0), lean_box(0), v___x_395_, v___f_394_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0(lean_object* v_inst_397_, lean_object* v_p_398_, lean_object* v_tail_399_, lean_object* v_toPure_400_, uint8_t v_____do__lift_401_){
_start:
{
if (v_____do__lift_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_toPure_400_);
v___x_402_ = l_List_anyM___redArg(v_inst_397_, v_p_398_, v_tail_399_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_tail_399_);
lean_dec(v_p_398_);
lean_dec_ref(v_inst_397_);
v___x_403_ = lean_box(v_____do__lift_401_);
v___x_404_ = lean_apply_2(v_toPure_400_, lean_box(0), v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM(lean_object* v_m_405_, lean_object* v_inst_406_, lean_object* v_00_u03b1_407_, lean_object* v_p_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_List_anyM___redArg(v_inst_406_, v_p_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0___boxed(lean_object* v_toPure_411_, lean_object* v_inst_412_, lean_object* v_p_413_, lean_object* v_tail_414_, lean_object* v_____do__lift_415_){
_start:
{
uint8_t v_____do__lift_73__boxed_416_; lean_object* v_res_417_; 
v_____do__lift_73__boxed_416_ = lean_unbox(v_____do__lift_415_);
v_res_417_ = l_List_allM___redArg___lam__0(v_toPure_411_, v_inst_412_, v_p_413_, v_tail_414_, v_____do__lift_73__boxed_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg(lean_object* v_inst_418_, lean_object* v_p_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v_toApplicative_421_; lean_object* v_toPure_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_418_, 0);
lean_inc_ref(v_toApplicative_421_);
lean_dec(v_p_419_);
lean_dec_ref(v_inst_418_);
v_toPure_422_ = lean_ctor_get(v_toApplicative_421_, 1);
lean_inc(v_toPure_422_);
lean_dec_ref(v_toApplicative_421_);
v___x_423_ = 1;
v___x_424_ = lean_box(v___x_423_);
v___x_425_ = lean_apply_2(v_toPure_422_, lean_box(0), v___x_424_);
return v___x_425_;
}
else
{
lean_object* v_toApplicative_426_; lean_object* v_toBind_427_; lean_object* v_toPure_428_; lean_object* v_head_429_; lean_object* v_tail_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_toApplicative_426_ = lean_ctor_get(v_inst_418_, 0);
v_toBind_427_ = lean_ctor_get(v_inst_418_, 1);
lean_inc(v_toBind_427_);
v_toPure_428_ = lean_ctor_get(v_toApplicative_426_, 1);
lean_inc(v_toPure_428_);
v_head_429_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_head_429_);
v_tail_430_ = lean_ctor_get(v_x_420_, 1);
lean_inc(v_tail_430_);
lean_dec_ref_known(v_x_420_, 2);
lean_inc(v_p_419_);
v___f_431_ = lean_alloc_closure((void*)(l_List_allM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_431_, 0, v_toPure_428_);
lean_closure_set(v___f_431_, 1, v_inst_418_);
lean_closure_set(v___f_431_, 2, v_p_419_);
lean_closure_set(v___f_431_, 3, v_tail_430_);
v___x_432_ = lean_apply_1(v_p_419_, v_head_429_);
v___x_433_ = lean_apply_4(v_toBind_427_, lean_box(0), lean_box(0), v___x_432_, v___f_431_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0(lean_object* v_toPure_434_, lean_object* v_inst_435_, lean_object* v_p_436_, lean_object* v_tail_437_, uint8_t v_____do__lift_438_){
_start:
{
if (v_____do__lift_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_tail_437_);
lean_dec(v_p_436_);
lean_dec_ref(v_inst_435_);
v___x_439_ = lean_box(v_____do__lift_438_);
v___x_440_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_toPure_434_);
v___x_441_ = l_List_allM___redArg(v_inst_435_, v_p_436_, v_tail_437_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM(lean_object* v_m_442_, lean_object* v_inst_443_, lean_object* v_00_u03b1_444_, lean_object* v_p_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_List_allM___redArg(v_inst_443_, v_p_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0___boxed(lean_object* v_inst_448_, lean_object* v_p_449_, lean_object* v_tail_450_, lean_object* v_head_451_, lean_object* v_toPure_452_, lean_object* v_____do__lift_453_){
_start:
{
uint8_t v_____do__lift_76__boxed_454_; lean_object* v_res_455_; 
v_____do__lift_76__boxed_454_ = lean_unbox(v_____do__lift_453_);
v_res_455_ = l_List_findM_x3f___redArg___lam__0(v_inst_448_, v_p_449_, v_tail_450_, v_head_451_, v_toPure_452_, v_____do__lift_76__boxed_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg(lean_object* v_inst_456_, lean_object* v_p_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v_toApplicative_459_; lean_object* v_toPure_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_toApplicative_459_ = lean_ctor_get(v_inst_456_, 0);
lean_inc_ref(v_toApplicative_459_);
lean_dec(v_p_457_);
lean_dec_ref(v_inst_456_);
v_toPure_460_ = lean_ctor_get(v_toApplicative_459_, 1);
lean_inc(v_toPure_460_);
lean_dec_ref(v_toApplicative_459_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_apply_2(v_toPure_460_, lean_box(0), v___x_461_);
return v___x_462_;
}
else
{
lean_object* v_toApplicative_463_; lean_object* v_toBind_464_; lean_object* v_toPure_465_; lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_toApplicative_463_ = lean_ctor_get(v_inst_456_, 0);
v_toBind_464_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_toBind_464_);
v_toPure_465_ = lean_ctor_get(v_toApplicative_463_, 1);
lean_inc(v_toPure_465_);
v_head_466_ = lean_ctor_get(v_x_458_, 0);
lean_inc_n(v_head_466_, 2);
v_tail_467_ = lean_ctor_get(v_x_458_, 1);
lean_inc(v_tail_467_);
lean_dec_ref_known(v_x_458_, 2);
lean_inc(v_p_457_);
v___f_468_ = lean_alloc_closure((void*)(l_List_findM_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_468_, 0, v_inst_456_);
lean_closure_set(v___f_468_, 1, v_p_457_);
lean_closure_set(v___f_468_, 2, v_tail_467_);
lean_closure_set(v___f_468_, 3, v_head_466_);
lean_closure_set(v___f_468_, 4, v_toPure_465_);
v___x_469_ = lean_apply_1(v_p_457_, v_head_466_);
v___x_470_ = lean_apply_4(v_toBind_464_, lean_box(0), lean_box(0), v___x_469_, v___f_468_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0(lean_object* v_inst_471_, lean_object* v_p_472_, lean_object* v_tail_473_, lean_object* v_head_474_, lean_object* v_toPure_475_, uint8_t v_____do__lift_476_){
_start:
{
if (v_____do__lift_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_toPure_475_);
lean_dec(v_head_474_);
v___x_477_ = l_List_findM_x3f___redArg(v_inst_471_, v_p_472_, v_tail_473_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_tail_473_);
lean_dec(v_p_472_);
lean_dec_ref(v_inst_471_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_head_474_);
v___x_479_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f(lean_object* v_m_480_, lean_object* v_inst_481_, lean_object* v_00_u03b1_482_, lean_object* v_p_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_List_findM_x3f___redArg(v_inst_481_, v_p_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_){
_start:
{
if (v_____do__lift_486_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_h__1_487_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_apply_1(v_h__2_488_, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_488_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_apply_1(v_h__1_487_, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_493_, lean_object* v_h__1_494_, lean_object* v_h__2_495_){
_start:
{
uint8_t v_____do__lift_24__boxed_496_; lean_object* v_res_497_; 
v_____do__lift_24__boxed_496_ = lean_unbox(v_____do__lift_493_);
v_res_497_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_24__boxed_496_, v_h__1_494_, v_h__2_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_object* v_motive_498_, uint8_t v_____do__lift_499_, lean_object* v_h__1_500_, lean_object* v_h__2_501_){
_start:
{
if (v_____do__lift_499_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_h__1_500_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_apply_1(v_h__2_501_, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_h__2_501_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_apply_1(v_h__1_500_, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_506_, lean_object* v_____do__lift_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
uint8_t v_____do__lift_35__boxed_510_; lean_object* v_res_511_; 
v_____do__lift_35__boxed_510_ = lean_unbox(v_____do__lift_507_);
v_res_511_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(v_motive_506_, v_____do__lift_35__boxed_510_, v_h__1_508_, v_h__2_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(uint8_t v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
if (v_x_512_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_h__1_513_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_h__2_514_, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_514_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v_h__1_513_, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
uint8_t v_x_24__boxed_522_; lean_object* v_res_523_; 
v_x_24__boxed_522_ = lean_unbox(v_x_519_);
v_res_523_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_522_, v_h__1_520_, v_h__2_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_object* v_motive_524_, uint8_t v_x_525_, lean_object* v_h__1_526_, lean_object* v_h__2_527_){
_start:
{
if (v_x_525_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_h__1_526_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_apply_1(v_h__2_527_, v___x_528_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v_h__2_527_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_apply_1(v_h__1_526_, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_532_, lean_object* v_x_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_){
_start:
{
uint8_t v_x_35__boxed_536_; lean_object* v_res_537_; 
v_x_35__boxed_536_ = lean_unbox(v_x_533_);
v_res_537_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(v_motive_532_, v_x_35__boxed_536_, v_h__1_534_, v_h__2_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg(lean_object* v_inst_538_, lean_object* v_f_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_toApplicative_541_; lean_object* v_toPure_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_toApplicative_541_ = lean_ctor_get(v_inst_538_, 0);
lean_inc_ref(v_toApplicative_541_);
lean_dec(v_f_539_);
lean_dec_ref(v_inst_538_);
v_toPure_542_ = lean_ctor_get(v_toApplicative_541_, 1);
lean_inc(v_toPure_542_);
lean_dec_ref(v_toApplicative_541_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_2(v_toPure_542_, lean_box(0), v___x_543_);
return v___x_544_;
}
else
{
lean_object* v_toApplicative_545_; lean_object* v_toBind_546_; lean_object* v_toPure_547_; lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toApplicative_545_ = lean_ctor_get(v_inst_538_, 0);
v_toBind_546_ = lean_ctor_get(v_inst_538_, 1);
lean_inc(v_toBind_546_);
v_toPure_547_ = lean_ctor_get(v_toApplicative_545_, 1);
lean_inc(v_toPure_547_);
v_head_548_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_head_548_);
v_tail_549_ = lean_ctor_get(v_x_540_, 1);
lean_inc(v_tail_549_);
lean_dec_ref_known(v_x_540_, 2);
lean_inc(v_f_539_);
v___f_550_ = lean_alloc_closure((void*)(l_List_findSomeM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_550_, 0, v_inst_538_);
lean_closure_set(v___f_550_, 1, v_f_539_);
lean_closure_set(v___f_550_, 2, v_tail_549_);
lean_closure_set(v___f_550_, 3, v_toPure_547_);
v___x_551_ = lean_apply_1(v_f_539_, v_head_548_);
v___x_552_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_551_, v___f_550_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg___lam__0(lean_object* v_inst_553_, lean_object* v_f_554_, lean_object* v_tail_555_, lean_object* v_toPure_556_, lean_object* v_____do__lift_557_){
_start:
{
if (lean_obj_tag(v_____do__lift_557_) == 0)
{
lean_object* v___x_558_; 
lean_dec(v_toPure_556_);
v___x_558_ = l_List_findSomeM_x3f___redArg(v_inst_553_, v_f_554_, v_tail_555_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_dec(v_tail_555_);
lean_dec(v_f_554_);
lean_dec_ref(v_inst_553_);
v___x_559_ = lean_apply_2(v_toPure_556_, lean_box(0), v_____do__lift_557_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f(lean_object* v_m_560_, lean_object* v_inst_561_, lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_f_564_, lean_object* v_x_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_List_findSomeM_x3f___redArg(v_inst_561_, v_f_564_, v_x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_){
_start:
{
if (lean_obj_tag(v_____do__lift_567_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_h__1_568_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v_h__2_569_, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_573_; 
lean_dec(v_h__2_569_);
v_val_572_ = lean_ctor_get(v_____do__lift_567_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_____do__lift_567_, 1);
v___x_573_ = lean_apply_1(v_h__1_568_, v_val_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_574_, lean_object* v_motive_575_, lean_object* v_____do__lift_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
if (lean_obj_tag(v_____do__lift_576_) == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_h__1_577_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_h__2_578_, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_582_; 
lean_dec(v_h__2_578_);
v_val_581_ = lean_ctor_get(v_____do__lift_576_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_____do__lift_576_, 1);
v___x_582_ = lean_apply_1(v_h__1_577_, v_val_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_583_, lean_object* v_h__1_584_, lean_object* v_h__2_585_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_h__1_584_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_apply_1(v_h__2_585_, v___x_586_);
return v___x_587_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_589_; 
lean_dec(v_h__2_585_);
v_val_588_ = lean_ctor_get(v_x_583_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v_x_583_, 1);
v___x_589_ = lean_apply_1(v_h__1_584_, v_val_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_590_, lean_object* v_motive_591_, lean_object* v_x_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_h__1_593_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_apply_1(v_h__2_594_, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_598_; 
lean_dec(v_h__2_594_);
v_val_597_ = lean_ctor_get(v_x_592_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_x_592_, 1);
v___x_598_ = lean_apply_1(v_h__1_593_, v_val_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toPure_599_, lean_object* v_inst_600_, lean_object* v_f_601_, lean_object* v_tail_602_, lean_object* v_____do__lift_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_List_forIn_x27_loop___redArg___lam__0(v_toPure_599_, v_inst_600_, v_f_601_, v_tail_602_, v_____do__lift_603_);
lean_dec(v_tail_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object* v_inst_605_, lean_object* v_f_606_, lean_object* v_as_x27_607_, lean_object* v_b_608_){
_start:
{
if (lean_obj_tag(v_as_x27_607_) == 0)
{
lean_object* v_toApplicative_609_; lean_object* v_toPure_610_; lean_object* v___x_611_; 
v_toApplicative_609_ = lean_ctor_get(v_inst_605_, 0);
lean_inc_ref(v_toApplicative_609_);
lean_dec(v_f_606_);
lean_dec_ref(v_inst_605_);
v_toPure_610_ = lean_ctor_get(v_toApplicative_609_, 1);
lean_inc(v_toPure_610_);
lean_dec_ref(v_toApplicative_609_);
v___x_611_ = lean_apply_2(v_toPure_610_, lean_box(0), v_b_608_);
return v___x_611_;
}
else
{
lean_object* v_toApplicative_612_; lean_object* v_toBind_613_; lean_object* v_toPure_614_; lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_toApplicative_612_ = lean_ctor_get(v_inst_605_, 0);
v_toBind_613_ = lean_ctor_get(v_inst_605_, 1);
lean_inc(v_toBind_613_);
v_toPure_614_ = lean_ctor_get(v_toApplicative_612_, 1);
lean_inc(v_toPure_614_);
v_head_615_ = lean_ctor_get(v_as_x27_607_, 0);
v_tail_616_ = lean_ctor_get(v_as_x27_607_, 1);
lean_inc(v_tail_616_);
lean_inc(v_f_606_);
v___f_617_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_617_, 0, v_toPure_614_);
lean_closure_set(v___f_617_, 1, v_inst_605_);
lean_closure_set(v___f_617_, 2, v_f_606_);
lean_closure_set(v___f_617_, 3, v_tail_616_);
lean_inc(v_head_615_);
v___x_618_ = lean_apply_3(v_f_606_, v_head_615_, lean_box(0), v_b_608_);
v___x_619_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v___x_618_, v___f_617_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_620_, lean_object* v_inst_621_, lean_object* v_f_622_, lean_object* v_tail_623_, lean_object* v_____do__lift_624_){
_start:
{
if (lean_obj_tag(v_____do__lift_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; 
lean_dec(v_f_622_);
lean_dec_ref(v_inst_621_);
v_a_625_ = lean_ctor_get(v_____do__lift_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v_____do__lift_624_, 1);
v___x_626_ = lean_apply_2(v_toPure_620_, lean_box(0), v_a_625_);
return v___x_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_628_; 
lean_dec(v_toPure_620_);
v_a_627_ = lean_ctor_get(v_____do__lift_624_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v_____do__lift_624_, 1);
v___x_628_ = l_List_forIn_x27_loop___redArg(v_inst_621_, v_f_622_, v_tail_623_, v_a_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___boxed(lean_object* v_inst_629_, lean_object* v_f_630_, lean_object* v_as_x27_631_, lean_object* v_b_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_List_forIn_x27_loop___redArg(v_inst_629_, v_f_630_, v_as_x27_631_, v_b_632_);
lean_dec(v_as_x27_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_m_636_, lean_object* v_inst_637_, lean_object* v_as_638_, lean_object* v_f_639_, lean_object* v_as_x27_640_, lean_object* v_b_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_List_forIn_x27_loop___redArg(v_inst_637_, v_f_639_, v_as_x27_640_, v_b_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_inst_647_, lean_object* v_as_648_, lean_object* v_f_649_, lean_object* v_as_x27_650_, lean_object* v_b_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_List_forIn_x27_loop(v_00_u03b1_644_, v_00_u03b2_645_, v_m_646_, v_inst_647_, v_as_648_, v_f_649_, v_as_x27_650_, v_b_651_, v_a_652_);
lean_dec(v_as_x27_650_);
lean_dec(v_as_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object* v_inst_654_, lean_object* v_as_655_, lean_object* v_init_656_, lean_object* v_f_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_List_forIn_x27_loop___redArg(v_inst_654_, v_f_657_, v_as_655_, v_init_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg___boxed(lean_object* v_inst_659_, lean_object* v_as_660_, lean_object* v_init_661_, lean_object* v_f_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_List_forIn_x27___redArg(v_inst_659_, v_as_660_, v_init_661_, v_f_662_);
lean_dec(v_as_660_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_m_666_, lean_object* v_inst_667_, lean_object* v_as_668_, lean_object* v_init_669_, lean_object* v_f_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_List_forIn_x27_loop___redArg(v_inst_667_, v_f_670_, v_as_668_, v_init_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___boxed(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_m_674_, lean_object* v_inst_675_, lean_object* v_as_676_, lean_object* v_init_677_, lean_object* v_f_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_List_forIn_x27(v_00_u03b1_672_, v_00_u03b2_673_, v_m_674_, v_inst_675_, v_as_676_, v_init_677_, v_f_678_);
lean_dec(v_as_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_680_, lean_object* v_00_u03b2_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_List_forIn_x27_loop___redArg(v_inst_680_, v___y_684_, v___y_682_, v___y_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object* v_inst_686_, lean_object* v_00_u03b2_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(v_inst_686_, v_00_u03b2_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_692_){
_start:
{
lean_object* v___f_693_; 
v___f_693_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_693_, 0, v_inst_692_);
return v___f_693_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_694_, lean_object* v_00_u03b1_695_, lean_object* v_inst_696_){
_start:
{
lean_object* v___f_697_; 
v___f_697_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_697_, 0, v_inst_696_);
return v___f_697_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad___redArg(lean_object* v_inst_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_699_, 0, lean_box(0));
lean_closure_set(v___x_699_, 1, v_inst_698_);
lean_closure_set(v___x_699_, 2, lean_box(0));
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad(lean_object* v_m_700_, lean_object* v_00_u03b1_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_703_, 0, lean_box(0));
lean_closure_set(v___x_703_, 1, v_inst_702_);
lean_closure_set(v___x_703_, 2, lean_box(0));
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_List_instFunctor___lam__0(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, lean_box(0));
lean_closure_set(v___x_708_, 2, v___y_706_);
v___x_709_ = lean_box(0);
v___x_710_ = l_List_mapTR_loop___redArg(v___x_708_, v___y_707_, v___x_709_);
return v___x_710_;
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
