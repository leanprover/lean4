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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_3_);
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
lean_dec_ref(v_x_49_);
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
lean_dec_ref(v_as_76_);
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
lean_dec_ref(v_as_100_);
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
lean_dec_ref(v_x_124_);
v_head_136_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_head_136_);
v_tail_137_ = lean_ctor_get(v_x_125_, 1);
lean_inc(v_tail_137_);
lean_dec_ref(v_x_125_);
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
lean_dec_ref(v_x_124_);
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
lean_inc(v_head_193_);
v_tail_194_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_tail_194_);
lean_dec_ref(v_x_187_);
lean_inc(v_head_193_);
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
lean_dec_ref(v_x_262_);
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
lean_dec_ref(v_x_307_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter___redArg(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v___x_335_; 
lean_dec(v_h__2_334_);
v___x_335_ = lean_apply_2(v_h__1_333_, v_x_330_, v_x_331_);
return v___x_335_;
}
else
{
lean_object* v_head_336_; lean_object* v_tail_337_; lean_object* v___x_338_; 
lean_dec(v_h__1_333_);
v_head_336_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_head_336_);
v_tail_337_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_tail_337_);
lean_dec_ref(v_x_332_);
v___x_338_ = lean_apply_4(v_h__2_334_, v_x_330_, v_x_331_, v_head_336_, v_tail_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter(lean_object* v_m_339_, lean_object* v_s_340_, lean_object* v_00_u03b1_341_, lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_348_; 
lean_dec(v_h__2_347_);
v___x_348_ = lean_apply_2(v_h__1_346_, v_x_343_, v_x_344_);
return v___x_348_;
}
else
{
lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_346_);
v_head_349_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_head_349_);
v_tail_350_ = lean_ctor_get(v_x_345_, 1);
lean_inc(v_tail_350_);
lean_dec_ref(v_x_345_);
v___x_351_ = lean_apply_4(v_h__2_347_, v_x_343_, v_x_344_, v_head_349_, v_tail_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg___lam__0(lean_object* v_f_352_, lean_object* v_s_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_apply_2(v_f_352_, v_a_354_, v_s_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg(lean_object* v_inst_356_, lean_object* v_f_357_, lean_object* v_init_358_, lean_object* v_l_359_){
_start:
{
lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___f_360_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_360_, 0, v_f_357_);
v___x_361_ = l_List_reverse___redArg(v_l_359_);
v___x_362_ = l_List_foldlM___redArg(v_inst_356_, v___f_360_, v_init_358_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM(lean_object* v_m_363_, lean_object* v_inst_364_, lean_object* v_s_365_, lean_object* v_00_u03b1_366_, lean_object* v_f_367_, lean_object* v_init_368_, lean_object* v_l_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___f_370_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_370_, 0, v_f_367_);
v___x_371_ = l_List_reverse___redArg(v_l_369_);
v___x_372_ = l_List_foldlM___redArg(v_inst_364_, v___f_370_, v_init_368_, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg(lean_object* v_inst_373_, lean_object* v_f_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v_failure_376_; lean_object* v___x_377_; 
lean_dec(v_f_374_);
v_failure_376_ = lean_ctor_get(v_inst_373_, 1);
lean_inc(v_failure_376_);
lean_dec_ref(v_inst_373_);
v___x_377_ = lean_apply_1(v_failure_376_, lean_box(0));
return v___x_377_;
}
else
{
lean_object* v_head_378_; lean_object* v_tail_379_; lean_object* v_orElse_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_head_378_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_head_378_);
v_tail_379_ = lean_ctor_get(v_x_375_, 1);
lean_inc(v_tail_379_);
lean_dec_ref(v_x_375_);
v_orElse_380_ = lean_ctor_get(v_inst_373_, 2);
lean_inc(v_orElse_380_);
lean_inc(v_f_374_);
v___f_381_ = lean_alloc_closure((void*)(l_List_firstM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_381_, 0, v_inst_373_);
lean_closure_set(v___f_381_, 1, v_f_374_);
lean_closure_set(v___f_381_, 2, v_tail_379_);
v___x_382_ = lean_apply_1(v_f_374_, v_head_378_);
v___x_383_ = lean_apply_3(v_orElse_380_, lean_box(0), v___x_382_, v___f_381_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg___lam__0(lean_object* v_inst_384_, lean_object* v_f_385_, lean_object* v_tail_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_List_firstM___redArg(v_inst_384_, v_f_385_, v_tail_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_List_firstM(lean_object* v_m_389_, lean_object* v_inst_390_, lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_f_393_, lean_object* v_x_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_List_firstM___redArg(v_inst_390_, v_f_393_, v_x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0___boxed(lean_object* v_inst_396_, lean_object* v_p_397_, lean_object* v_tail_398_, lean_object* v_toPure_399_, lean_object* v_____do__lift_400_){
_start:
{
uint8_t v_____do__lift_73__boxed_401_; lean_object* v_res_402_; 
v_____do__lift_73__boxed_401_ = lean_unbox(v_____do__lift_400_);
v_res_402_ = l_List_anyM___redArg___lam__0(v_inst_396_, v_p_397_, v_tail_398_, v_toPure_399_, v_____do__lift_73__boxed_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg(lean_object* v_inst_403_, lean_object* v_p_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_object* v_toApplicative_406_; lean_object* v_toPure_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_toApplicative_406_ = lean_ctor_get(v_inst_403_, 0);
lean_inc_ref(v_toApplicative_406_);
lean_dec(v_p_404_);
lean_dec_ref(v_inst_403_);
v_toPure_407_ = lean_ctor_get(v_toApplicative_406_, 1);
lean_inc(v_toPure_407_);
lean_dec_ref(v_toApplicative_406_);
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
v___x_410_ = lean_apply_2(v_toPure_407_, lean_box(0), v___x_409_);
return v___x_410_;
}
else
{
lean_object* v_toApplicative_411_; lean_object* v_toBind_412_; lean_object* v_toPure_413_; lean_object* v_head_414_; lean_object* v_tail_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_toApplicative_411_ = lean_ctor_get(v_inst_403_, 0);
v_toBind_412_ = lean_ctor_get(v_inst_403_, 1);
lean_inc(v_toBind_412_);
v_toPure_413_ = lean_ctor_get(v_toApplicative_411_, 1);
lean_inc(v_toPure_413_);
v_head_414_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_head_414_);
v_tail_415_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_tail_415_);
lean_dec_ref(v_x_405_);
lean_inc(v_p_404_);
v___f_416_ = lean_alloc_closure((void*)(l_List_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_416_, 0, v_inst_403_);
lean_closure_set(v___f_416_, 1, v_p_404_);
lean_closure_set(v___f_416_, 2, v_tail_415_);
lean_closure_set(v___f_416_, 3, v_toPure_413_);
v___x_417_ = lean_apply_1(v_p_404_, v_head_414_);
v___x_418_ = lean_apply_4(v_toBind_412_, lean_box(0), lean_box(0), v___x_417_, v___f_416_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0(lean_object* v_inst_419_, lean_object* v_p_420_, lean_object* v_tail_421_, lean_object* v_toPure_422_, uint8_t v_____do__lift_423_){
_start:
{
if (v_____do__lift_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec(v_toPure_422_);
v___x_424_ = l_List_anyM___redArg(v_inst_419_, v_p_420_, v_tail_421_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_tail_421_);
lean_dec(v_p_420_);
lean_dec_ref(v_inst_419_);
v___x_425_ = lean_box(v_____do__lift_423_);
v___x_426_ = lean_apply_2(v_toPure_422_, lean_box(0), v___x_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM(lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_00_u03b1_429_, lean_object* v_p_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_List_anyM___redArg(v_inst_428_, v_p_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0___boxed(lean_object* v_toPure_433_, lean_object* v_inst_434_, lean_object* v_p_435_, lean_object* v_tail_436_, lean_object* v_____do__lift_437_){
_start:
{
uint8_t v_____do__lift_73__boxed_438_; lean_object* v_res_439_; 
v_____do__lift_73__boxed_438_ = lean_unbox(v_____do__lift_437_);
v_res_439_ = l_List_allM___redArg___lam__0(v_toPure_433_, v_inst_434_, v_p_435_, v_tail_436_, v_____do__lift_73__boxed_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg(lean_object* v_inst_440_, lean_object* v_p_441_, lean_object* v_x_442_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_object* v_toApplicative_443_; lean_object* v_toPure_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_toApplicative_443_ = lean_ctor_get(v_inst_440_, 0);
lean_inc_ref(v_toApplicative_443_);
lean_dec(v_p_441_);
lean_dec_ref(v_inst_440_);
v_toPure_444_ = lean_ctor_get(v_toApplicative_443_, 1);
lean_inc(v_toPure_444_);
lean_dec_ref(v_toApplicative_443_);
v___x_445_ = 1;
v___x_446_ = lean_box(v___x_445_);
v___x_447_ = lean_apply_2(v_toPure_444_, lean_box(0), v___x_446_);
return v___x_447_;
}
else
{
lean_object* v_toApplicative_448_; lean_object* v_toBind_449_; lean_object* v_toPure_450_; lean_object* v_head_451_; lean_object* v_tail_452_; lean_object* v___f_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_toApplicative_448_ = lean_ctor_get(v_inst_440_, 0);
v_toBind_449_ = lean_ctor_get(v_inst_440_, 1);
lean_inc(v_toBind_449_);
v_toPure_450_ = lean_ctor_get(v_toApplicative_448_, 1);
lean_inc(v_toPure_450_);
v_head_451_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_head_451_);
v_tail_452_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_tail_452_);
lean_dec_ref(v_x_442_);
lean_inc(v_p_441_);
v___f_453_ = lean_alloc_closure((void*)(l_List_allM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_453_, 0, v_toPure_450_);
lean_closure_set(v___f_453_, 1, v_inst_440_);
lean_closure_set(v___f_453_, 2, v_p_441_);
lean_closure_set(v___f_453_, 3, v_tail_452_);
v___x_454_ = lean_apply_1(v_p_441_, v_head_451_);
v___x_455_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v___x_454_, v___f_453_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0(lean_object* v_toPure_456_, lean_object* v_inst_457_, lean_object* v_p_458_, lean_object* v_tail_459_, uint8_t v_____do__lift_460_){
_start:
{
if (v_____do__lift_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_tail_459_);
lean_dec(v_p_458_);
lean_dec_ref(v_inst_457_);
v___x_461_ = lean_box(v_____do__lift_460_);
v___x_462_ = lean_apply_2(v_toPure_456_, lean_box(0), v___x_461_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_toPure_456_);
v___x_463_ = l_List_allM___redArg(v_inst_457_, v_p_458_, v_tail_459_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM(lean_object* v_m_464_, lean_object* v_inst_465_, lean_object* v_00_u03b1_466_, lean_object* v_p_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_List_allM___redArg(v_inst_465_, v_p_467_, v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0___boxed(lean_object* v_inst_470_, lean_object* v_p_471_, lean_object* v_tail_472_, lean_object* v_head_473_, lean_object* v_toPure_474_, lean_object* v_____do__lift_475_){
_start:
{
uint8_t v_____do__lift_76__boxed_476_; lean_object* v_res_477_; 
v_____do__lift_76__boxed_476_ = lean_unbox(v_____do__lift_475_);
v_res_477_ = l_List_findM_x3f___redArg___lam__0(v_inst_470_, v_p_471_, v_tail_472_, v_head_473_, v_toPure_474_, v_____do__lift_76__boxed_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg(lean_object* v_inst_478_, lean_object* v_p_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_toApplicative_481_; lean_object* v_toPure_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc_ref(v_toApplicative_481_);
lean_dec(v_p_479_);
lean_dec_ref(v_inst_478_);
v_toPure_482_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_482_);
lean_dec_ref(v_toApplicative_481_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_483_);
return v___x_484_;
}
else
{
lean_object* v_toApplicative_485_; lean_object* v_toBind_486_; lean_object* v_toPure_487_; lean_object* v_head_488_; lean_object* v_tail_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_toApplicative_485_ = lean_ctor_get(v_inst_478_, 0);
v_toBind_486_ = lean_ctor_get(v_inst_478_, 1);
lean_inc(v_toBind_486_);
v_toPure_487_ = lean_ctor_get(v_toApplicative_485_, 1);
lean_inc(v_toPure_487_);
v_head_488_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_head_488_);
v_tail_489_ = lean_ctor_get(v_x_480_, 1);
lean_inc(v_tail_489_);
lean_dec_ref(v_x_480_);
lean_inc(v_head_488_);
lean_inc(v_p_479_);
v___f_490_ = lean_alloc_closure((void*)(l_List_findM_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_490_, 0, v_inst_478_);
lean_closure_set(v___f_490_, 1, v_p_479_);
lean_closure_set(v___f_490_, 2, v_tail_489_);
lean_closure_set(v___f_490_, 3, v_head_488_);
lean_closure_set(v___f_490_, 4, v_toPure_487_);
v___x_491_ = lean_apply_1(v_p_479_, v_head_488_);
v___x_492_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_491_, v___f_490_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0(lean_object* v_inst_493_, lean_object* v_p_494_, lean_object* v_tail_495_, lean_object* v_head_496_, lean_object* v_toPure_497_, uint8_t v_____do__lift_498_){
_start:
{
if (v_____do__lift_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_toPure_497_);
lean_dec(v_head_496_);
v___x_499_ = l_List_findM_x3f___redArg(v_inst_493_, v_p_494_, v_tail_495_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_tail_495_);
lean_dec(v_p_494_);
lean_dec_ref(v_inst_493_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_head_496_);
v___x_501_ = lean_apply_2(v_toPure_497_, lean_box(0), v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f(lean_object* v_m_502_, lean_object* v_inst_503_, lean_object* v_00_u03b1_504_, lean_object* v_p_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_List_findM_x3f___redArg(v_inst_503_, v_p_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__2_510_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__1_509_, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_head_513_; lean_object* v_tail_514_; lean_object* v___x_515_; 
lean_dec(v_h__1_509_);
v_head_513_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_head_513_);
v_tail_514_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_tail_514_);
lean_dec_ref(v_x_508_);
v___x_515_ = lean_apply_2(v_h__2_510_, v_head_513_, v_tail_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter(lean_object* v_00_u03b1_516_, lean_object* v_motive_517_, lean_object* v_x_518_, lean_object* v_h__1_519_, lean_object* v_h__2_520_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_h__2_520_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_1(v_h__1_519_, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_head_523_; lean_object* v_tail_524_; lean_object* v___x_525_; 
lean_dec(v_h__1_519_);
v_head_523_ = lean_ctor_get(v_x_518_, 0);
lean_inc(v_head_523_);
v_tail_524_ = lean_ctor_get(v_x_518_, 1);
lean_inc(v_tail_524_);
lean_dec_ref(v_x_518_);
v___x_525_ = lean_apply_2(v_h__2_520_, v_head_523_, v_tail_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
if (v_____do__lift_526_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_h__1_527_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_1(v_h__2_528_, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_h__2_528_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_apply_1(v_h__1_527_, v___x_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_533_, lean_object* v_h__1_534_, lean_object* v_h__2_535_){
_start:
{
uint8_t v_____do__lift_26__boxed_536_; lean_object* v_res_537_; 
v_____do__lift_26__boxed_536_ = lean_unbox(v_____do__lift_533_);
v_res_537_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_26__boxed_536_, v_h__1_534_, v_h__2_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_object* v_motive_538_, uint8_t v_____do__lift_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_){
_start:
{
if (v_____do__lift_539_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_h__1_540_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_apply_1(v_h__2_541_, v___x_542_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_h__2_541_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_apply_1(v_h__1_540_, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_546_, lean_object* v_____do__lift_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
uint8_t v_____do__lift_37__boxed_550_; lean_object* v_res_551_; 
v_____do__lift_37__boxed_550_ = lean_unbox(v_____do__lift_547_);
v_res_551_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(v_motive_546_, v_____do__lift_37__boxed_550_, v_h__1_548_, v_h__2_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(uint8_t v_x_552_, lean_object* v_h__1_553_, lean_object* v_h__2_554_){
_start:
{
if (v_x_552_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_h__1_553_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_1(v_h__2_554_, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_h__2_554_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_1(v_h__1_553_, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_559_, lean_object* v_h__1_560_, lean_object* v_h__2_561_){
_start:
{
uint8_t v_x_26__boxed_562_; lean_object* v_res_563_; 
v_x_26__boxed_562_ = lean_unbox(v_x_559_);
v_res_563_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_562_, v_h__1_560_, v_h__2_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_object* v_motive_564_, uint8_t v_x_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
if (v_x_565_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_h__1_566_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_apply_1(v_h__2_567_, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_h__2_567_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_1(v_h__1_566_, v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_572_, lean_object* v_x_573_, lean_object* v_h__1_574_, lean_object* v_h__2_575_){
_start:
{
uint8_t v_x_37__boxed_576_; lean_object* v_res_577_; 
v_x_37__boxed_576_ = lean_unbox(v_x_573_);
v_res_577_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(v_motive_572_, v_x_37__boxed_576_, v_h__1_574_, v_h__2_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg(lean_object* v_inst_578_, lean_object* v_f_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v_toApplicative_581_; lean_object* v_toPure_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_toApplicative_581_ = lean_ctor_get(v_inst_578_, 0);
lean_inc_ref(v_toApplicative_581_);
lean_dec(v_f_579_);
lean_dec_ref(v_inst_578_);
v_toPure_582_ = lean_ctor_get(v_toApplicative_581_, 1);
lean_inc(v_toPure_582_);
lean_dec_ref(v_toApplicative_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_apply_2(v_toPure_582_, lean_box(0), v___x_583_);
return v___x_584_;
}
else
{
lean_object* v_toApplicative_585_; lean_object* v_toBind_586_; lean_object* v_toPure_587_; lean_object* v_head_588_; lean_object* v_tail_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_toApplicative_585_ = lean_ctor_get(v_inst_578_, 0);
v_toBind_586_ = lean_ctor_get(v_inst_578_, 1);
lean_inc(v_toBind_586_);
v_toPure_587_ = lean_ctor_get(v_toApplicative_585_, 1);
lean_inc(v_toPure_587_);
v_head_588_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_head_588_);
v_tail_589_ = lean_ctor_get(v_x_580_, 1);
lean_inc(v_tail_589_);
lean_dec_ref(v_x_580_);
lean_inc(v_f_579_);
v___f_590_ = lean_alloc_closure((void*)(l_List_findSomeM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_590_, 0, v_inst_578_);
lean_closure_set(v___f_590_, 1, v_f_579_);
lean_closure_set(v___f_590_, 2, v_tail_589_);
lean_closure_set(v___f_590_, 3, v_toPure_587_);
v___x_591_ = lean_apply_1(v_f_579_, v_head_588_);
v___x_592_ = lean_apply_4(v_toBind_586_, lean_box(0), lean_box(0), v___x_591_, v___f_590_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg___lam__0(lean_object* v_inst_593_, lean_object* v_f_594_, lean_object* v_tail_595_, lean_object* v_toPure_596_, lean_object* v_____do__lift_597_){
_start:
{
if (lean_obj_tag(v_____do__lift_597_) == 0)
{
lean_object* v___x_598_; 
lean_dec(v_toPure_596_);
v___x_598_ = l_List_findSomeM_x3f___redArg(v_inst_593_, v_f_594_, v_tail_595_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; 
lean_dec(v_tail_595_);
lean_dec(v_f_594_);
lean_dec_ref(v_inst_593_);
v___x_599_ = lean_apply_2(v_toPure_596_, lean_box(0), v_____do__lift_597_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f(lean_object* v_m_600_, lean_object* v_inst_601_, lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_f_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_List_findSomeM_x3f___redArg(v_inst_601_, v_f_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_607_, lean_object* v_h__1_608_, lean_object* v_h__2_609_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_h__2_609_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_apply_1(v_h__1_608_, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_head_612_; lean_object* v_tail_613_; lean_object* v___x_614_; 
lean_dec(v_h__1_608_);
v_head_612_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_head_612_);
v_tail_613_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_tail_613_);
lean_dec_ref(v_x_607_);
v___x_614_ = lean_apply_2(v_h__2_609_, v_head_612_, v_tail_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_615_, lean_object* v_motive_616_, lean_object* v_x_617_, lean_object* v_h__1_618_, lean_object* v_h__2_619_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_h__2_619_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_1(v_h__1_618_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_624_; 
lean_dec(v_h__1_618_);
v_head_622_ = lean_ctor_get(v_x_617_, 0);
lean_inc(v_head_622_);
v_tail_623_ = lean_ctor_get(v_x_617_, 1);
lean_inc(v_tail_623_);
lean_dec_ref(v_x_617_);
v___x_624_ = lean_apply_2(v_h__2_619_, v_head_622_, v_tail_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_625_, lean_object* v_h__1_626_, lean_object* v_h__2_627_){
_start:
{
if (lean_obj_tag(v_____do__lift_625_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_h__1_626_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_1(v_h__2_627_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_631_; 
lean_dec(v_h__2_627_);
v_val_630_ = lean_ctor_get(v_____do__lift_625_, 0);
lean_inc(v_val_630_);
lean_dec_ref(v_____do__lift_625_);
v___x_631_ = lean_apply_1(v_h__1_626_, v_val_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_632_, lean_object* v_motive_633_, lean_object* v_____do__lift_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
if (lean_obj_tag(v_____do__lift_634_) == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_h__1_635_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_apply_1(v_h__2_636_, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_640_; 
lean_dec(v_h__2_636_);
v_val_639_ = lean_ctor_get(v_____do__lift_634_, 0);
lean_inc(v_val_639_);
lean_dec_ref(v_____do__lift_634_);
v___x_640_ = lean_apply_1(v_h__1_635_, v_val_639_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_641_, lean_object* v_h__1_642_, lean_object* v_h__2_643_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_h__2_643_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_apply_1(v_h__1_642_, v___x_644_);
return v___x_645_;
}
else
{
lean_object* v_head_646_; lean_object* v_tail_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_642_);
v_head_646_ = lean_ctor_get(v_x_641_, 0);
lean_inc(v_head_646_);
v_tail_647_ = lean_ctor_get(v_x_641_, 1);
lean_inc(v_tail_647_);
lean_dec_ref(v_x_641_);
v___x_648_ = lean_apply_2(v_h__2_643_, v_head_646_, v_tail_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_649_, lean_object* v_motive_650_, lean_object* v_x_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v_h__2_653_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_apply_1(v_h__1_652_, v___x_654_);
return v___x_655_;
}
else
{
lean_object* v_head_656_; lean_object* v_tail_657_; lean_object* v___x_658_; 
lean_dec(v_h__1_652_);
v_head_656_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_head_656_);
v_tail_657_ = lean_ctor_get(v_x_651_, 1);
lean_inc(v_tail_657_);
lean_dec_ref(v_x_651_);
v___x_658_ = lean_apply_2(v_h__2_653_, v_head_656_, v_tail_657_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_h__1_660_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_1(v_h__2_661_, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v_val_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_661_);
v_val_664_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_val_664_);
lean_dec_ref(v_x_659_);
v___x_665_ = lean_apply_1(v_h__1_660_, v_val_664_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_666_, lean_object* v_motive_667_, lean_object* v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_h__1_669_);
v___x_671_ = lean_box(0);
v___x_672_ = lean_apply_1(v_h__2_670_, v___x_671_);
return v___x_672_;
}
else
{
lean_object* v_val_673_; lean_object* v___x_674_; 
lean_dec(v_h__2_670_);
v_val_673_ = lean_ctor_get(v_x_668_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_x_668_);
v___x_674_ = lean_apply_1(v_h__1_669_, v_val_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object* v_inst_675_, lean_object* v_f_676_, lean_object* v_as_x27_677_, lean_object* v_b_678_){
_start:
{
if (lean_obj_tag(v_as_x27_677_) == 0)
{
lean_object* v_toApplicative_679_; lean_object* v_toPure_680_; lean_object* v___x_681_; 
v_toApplicative_679_ = lean_ctor_get(v_inst_675_, 0);
lean_inc_ref(v_toApplicative_679_);
lean_dec(v_f_676_);
lean_dec_ref(v_inst_675_);
v_toPure_680_ = lean_ctor_get(v_toApplicative_679_, 1);
lean_inc(v_toPure_680_);
lean_dec_ref(v_toApplicative_679_);
v___x_681_ = lean_apply_2(v_toPure_680_, lean_box(0), v_b_678_);
return v___x_681_;
}
else
{
lean_object* v_toApplicative_682_; lean_object* v_toBind_683_; lean_object* v_toPure_684_; lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v___f_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_toApplicative_682_ = lean_ctor_get(v_inst_675_, 0);
v_toBind_683_ = lean_ctor_get(v_inst_675_, 1);
lean_inc(v_toBind_683_);
v_toPure_684_ = lean_ctor_get(v_toApplicative_682_, 1);
lean_inc(v_toPure_684_);
v_head_685_ = lean_ctor_get(v_as_x27_677_, 0);
lean_inc(v_head_685_);
v_tail_686_ = lean_ctor_get(v_as_x27_677_, 1);
lean_inc(v_tail_686_);
lean_dec_ref(v_as_x27_677_);
lean_inc(v_f_676_);
v___f_687_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_687_, 0, v_toPure_684_);
lean_closure_set(v___f_687_, 1, v_inst_675_);
lean_closure_set(v___f_687_, 2, v_f_676_);
lean_closure_set(v___f_687_, 3, v_tail_686_);
v___x_688_ = lean_apply_3(v_f_676_, v_head_685_, lean_box(0), v_b_678_);
v___x_689_ = lean_apply_4(v_toBind_683_, lean_box(0), lean_box(0), v___x_688_, v___f_687_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_690_, lean_object* v_inst_691_, lean_object* v_f_692_, lean_object* v_tail_693_, lean_object* v_____do__lift_694_){
_start:
{
if (lean_obj_tag(v_____do__lift_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
lean_dec(v_tail_693_);
lean_dec(v_f_692_);
lean_dec_ref(v_inst_691_);
v_a_695_ = lean_ctor_get(v_____do__lift_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v_____do__lift_694_);
v___x_696_ = lean_apply_2(v_toPure_690_, lean_box(0), v_a_695_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_698_; 
lean_dec(v_toPure_690_);
v_a_697_ = lean_ctor_get(v_____do__lift_694_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v_____do__lift_694_);
v___x_698_ = l_List_forIn_x27_loop___redArg(v_inst_691_, v_f_692_, v_tail_693_, v_a_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_m_701_, lean_object* v_inst_702_, lean_object* v_as_703_, lean_object* v_f_704_, lean_object* v_as_x27_705_, lean_object* v_b_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_List_forIn_x27_loop___redArg(v_inst_702_, v_f_704_, v_as_x27_705_, v_b_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_m_711_, lean_object* v_inst_712_, lean_object* v_as_713_, lean_object* v_f_714_, lean_object* v_as_x27_715_, lean_object* v_b_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_forIn_x27_loop(v_00_u03b1_709_, v_00_u03b2_710_, v_m_711_, v_inst_712_, v_as_713_, v_f_714_, v_as_x27_715_, v_b_716_, v_a_717_);
lean_dec(v_as_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object* v_inst_719_, lean_object* v_as_720_, lean_object* v_init_721_, lean_object* v_f_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_List_forIn_x27_loop___redArg(v_inst_719_, v_f_722_, v_as_720_, v_init_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_m_726_, lean_object* v_inst_727_, lean_object* v_as_728_, lean_object* v_init_729_, lean_object* v_f_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_List_forIn_x27_loop___redArg(v_inst_727_, v_f_730_, v_as_728_, v_init_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_732_, lean_object* v_00_u03b2_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_List_forIn_x27_loop___redArg(v_inst_732_, v___y_736_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_738_){
_start:
{
lean_object* v___f_739_; 
v___f_739_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_739_, 0, v_inst_738_);
return v___f_739_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_740_, lean_object* v_00_u03b1_741_, lean_object* v_inst_742_){
_start:
{
lean_object* v___f_743_; 
v___f_743_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_743_, 0, v_inst_742_);
return v___f_743_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad___redArg(lean_object* v_inst_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, v_inst_744_);
lean_closure_set(v___x_745_, 2, lean_box(0));
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad(lean_object* v_m_746_, lean_object* v_00_u03b1_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_749_, 0, lean_box(0));
lean_closure_set(v___x_749_, 1, v_inst_748_);
lean_closure_set(v___x_749_, 2, lean_box(0));
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_List_instFunctor___lam__0(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, lean_box(0));
lean_closure_set(v___x_754_, 2, v___y_752_);
v___x_755_ = lean_box(0);
v___x_756_ = l_List_mapTR_loop___redArg(v___x_754_, v___y_753_, v___x_755_);
return v___x_756_;
}
}
lean_object* runtime_initialize_Init_Control_Lawful(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
