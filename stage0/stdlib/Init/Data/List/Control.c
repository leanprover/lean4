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
lean_object* v___x_348_; 
v___x_348_ = l___private_Init_Data_List_Control_0__List_foldlM_match__1_splitter___redArg(v_x_343_, v_x_344_, v_x_345_, v_h__1_346_, v_h__2_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg___lam__0(lean_object* v_f_349_, lean_object* v_s_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_2(v_f_349_, v_a_351_, v_s_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM___redArg(lean_object* v_inst_353_, lean_object* v_f_354_, lean_object* v_init_355_, lean_object* v_l_356_){
_start:
{
lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___f_357_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_357_, 0, v_f_354_);
v___x_358_ = l_List_reverse___redArg(v_l_356_);
v___x_359_ = l_List_foldlM___redArg(v_inst_353_, v___f_357_, v_init_355_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_List_foldrM(lean_object* v_m_360_, lean_object* v_inst_361_, lean_object* v_s_362_, lean_object* v_00_u03b1_363_, lean_object* v_f_364_, lean_object* v_init_365_, lean_object* v_l_366_){
_start:
{
lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___f_367_ = lean_alloc_closure((void*)(l_List_foldrM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_367_, 0, v_f_364_);
v___x_368_ = l_List_reverse___redArg(v_l_366_);
v___x_369_ = l_List_foldlM___redArg(v_inst_361_, v___f_367_, v_init_365_, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg(lean_object* v_inst_370_, lean_object* v_f_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_failure_373_; lean_object* v___x_374_; 
lean_dec(v_f_371_);
v_failure_373_ = lean_ctor_get(v_inst_370_, 1);
lean_inc(v_failure_373_);
lean_dec_ref(v_inst_370_);
v___x_374_ = lean_apply_1(v_failure_373_, lean_box(0));
return v___x_374_;
}
else
{
lean_object* v_head_375_; lean_object* v_tail_376_; lean_object* v_orElse_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_head_375_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_head_375_);
v_tail_376_ = lean_ctor_get(v_x_372_, 1);
lean_inc(v_tail_376_);
lean_dec_ref(v_x_372_);
v_orElse_377_ = lean_ctor_get(v_inst_370_, 2);
lean_inc(v_orElse_377_);
lean_inc(v_f_371_);
v___f_378_ = lean_alloc_closure((void*)(l_List_firstM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_378_, 0, v_inst_370_);
lean_closure_set(v___f_378_, 1, v_f_371_);
lean_closure_set(v___f_378_, 2, v_tail_376_);
v___x_379_ = lean_apply_1(v_f_371_, v_head_375_);
v___x_380_ = lean_apply_3(v_orElse_377_, lean_box(0), v___x_379_, v___f_378_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___redArg___lam__0(lean_object* v_inst_381_, lean_object* v_f_382_, lean_object* v_tail_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_List_firstM___redArg(v_inst_381_, v_f_382_, v_tail_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_List_firstM(lean_object* v_m_386_, lean_object* v_inst_387_, lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_f_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_List_firstM___redArg(v_inst_387_, v_f_390_, v_x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0___boxed(lean_object* v_inst_393_, lean_object* v_p_394_, lean_object* v_tail_395_, lean_object* v_toPure_396_, lean_object* v_____do__lift_397_){
_start:
{
uint8_t v_____do__lift_73__boxed_398_; lean_object* v_res_399_; 
v_____do__lift_73__boxed_398_ = lean_unbox(v_____do__lift_397_);
v_res_399_ = l_List_anyM___redArg___lam__0(v_inst_393_, v_p_394_, v_tail_395_, v_toPure_396_, v_____do__lift_73__boxed_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg(lean_object* v_inst_400_, lean_object* v_p_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v_toApplicative_403_; lean_object* v_toPure_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_toApplicative_403_ = lean_ctor_get(v_inst_400_, 0);
lean_inc_ref(v_toApplicative_403_);
lean_dec(v_p_401_);
lean_dec_ref(v_inst_400_);
v_toPure_404_ = lean_ctor_get(v_toApplicative_403_, 1);
lean_inc(v_toPure_404_);
lean_dec_ref(v_toApplicative_403_);
v___x_405_ = 0;
v___x_406_ = lean_box(v___x_405_);
v___x_407_ = lean_apply_2(v_toPure_404_, lean_box(0), v___x_406_);
return v___x_407_;
}
else
{
lean_object* v_toApplicative_408_; lean_object* v_toBind_409_; lean_object* v_toPure_410_; lean_object* v_head_411_; lean_object* v_tail_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_toApplicative_408_ = lean_ctor_get(v_inst_400_, 0);
v_toBind_409_ = lean_ctor_get(v_inst_400_, 1);
lean_inc(v_toBind_409_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_408_, 1);
lean_inc(v_toPure_410_);
v_head_411_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_head_411_);
v_tail_412_ = lean_ctor_get(v_x_402_, 1);
lean_inc(v_tail_412_);
lean_dec_ref(v_x_402_);
lean_inc(v_p_401_);
v___f_413_ = lean_alloc_closure((void*)(l_List_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_413_, 0, v_inst_400_);
lean_closure_set(v___f_413_, 1, v_p_401_);
lean_closure_set(v___f_413_, 2, v_tail_412_);
lean_closure_set(v___f_413_, 3, v_toPure_410_);
v___x_414_ = lean_apply_1(v_p_401_, v_head_411_);
v___x_415_ = lean_apply_4(v_toBind_409_, lean_box(0), lean_box(0), v___x_414_, v___f_413_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___redArg___lam__0(lean_object* v_inst_416_, lean_object* v_p_417_, lean_object* v_tail_418_, lean_object* v_toPure_419_, uint8_t v_____do__lift_420_){
_start:
{
if (v_____do__lift_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec(v_toPure_419_);
v___x_421_ = l_List_anyM___redArg(v_inst_416_, v_p_417_, v_tail_418_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_tail_418_);
lean_dec(v_p_417_);
lean_dec_ref(v_inst_416_);
v___x_422_ = lean_box(v_____do__lift_420_);
v___x_423_ = lean_apply_2(v_toPure_419_, lean_box(0), v___x_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_List_anyM(lean_object* v_m_424_, lean_object* v_inst_425_, lean_object* v_00_u03b1_426_, lean_object* v_p_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_List_anyM___redArg(v_inst_425_, v_p_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0___boxed(lean_object* v_toPure_430_, lean_object* v_inst_431_, lean_object* v_p_432_, lean_object* v_tail_433_, lean_object* v_____do__lift_434_){
_start:
{
uint8_t v_____do__lift_73__boxed_435_; lean_object* v_res_436_; 
v_____do__lift_73__boxed_435_ = lean_unbox(v_____do__lift_434_);
v_res_436_ = l_List_allM___redArg___lam__0(v_toPure_430_, v_inst_431_, v_p_432_, v_tail_433_, v_____do__lift_73__boxed_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg(lean_object* v_inst_437_, lean_object* v_p_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v_toApplicative_440_; lean_object* v_toPure_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_toApplicative_440_ = lean_ctor_get(v_inst_437_, 0);
lean_inc_ref(v_toApplicative_440_);
lean_dec(v_p_438_);
lean_dec_ref(v_inst_437_);
v_toPure_441_ = lean_ctor_get(v_toApplicative_440_, 1);
lean_inc(v_toPure_441_);
lean_dec_ref(v_toApplicative_440_);
v___x_442_ = 1;
v___x_443_ = lean_box(v___x_442_);
v___x_444_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_toPure_447_; lean_object* v_head_448_; lean_object* v_tail_449_; lean_object* v___f_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_437_, 0);
v_toBind_446_ = lean_ctor_get(v_inst_437_, 1);
lean_inc(v_toBind_446_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_447_);
v_head_448_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_head_448_);
v_tail_449_ = lean_ctor_get(v_x_439_, 1);
lean_inc(v_tail_449_);
lean_dec_ref(v_x_439_);
lean_inc(v_p_438_);
v___f_450_ = lean_alloc_closure((void*)(l_List_allM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_450_, 0, v_toPure_447_);
lean_closure_set(v___f_450_, 1, v_inst_437_);
lean_closure_set(v___f_450_, 2, v_p_438_);
lean_closure_set(v___f_450_, 3, v_tail_449_);
v___x_451_ = lean_apply_1(v_p_438_, v_head_448_);
v___x_452_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v___x_451_, v___f_450_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___redArg___lam__0(lean_object* v_toPure_453_, lean_object* v_inst_454_, lean_object* v_p_455_, lean_object* v_tail_456_, uint8_t v_____do__lift_457_){
_start:
{
if (v_____do__lift_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_tail_456_);
lean_dec(v_p_455_);
lean_dec_ref(v_inst_454_);
v___x_458_ = lean_box(v_____do__lift_457_);
v___x_459_ = lean_apply_2(v_toPure_453_, lean_box(0), v___x_458_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
lean_dec(v_toPure_453_);
v___x_460_ = l_List_allM___redArg(v_inst_454_, v_p_455_, v_tail_456_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_List_allM(lean_object* v_m_461_, lean_object* v_inst_462_, lean_object* v_00_u03b1_463_, lean_object* v_p_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_List_allM___redArg(v_inst_462_, v_p_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0___boxed(lean_object* v_inst_467_, lean_object* v_p_468_, lean_object* v_tail_469_, lean_object* v_head_470_, lean_object* v_toPure_471_, lean_object* v_____do__lift_472_){
_start:
{
uint8_t v_____do__lift_76__boxed_473_; lean_object* v_res_474_; 
v_____do__lift_76__boxed_473_ = lean_unbox(v_____do__lift_472_);
v_res_474_ = l_List_findM_x3f___redArg___lam__0(v_inst_467_, v_p_468_, v_tail_469_, v_head_470_, v_toPure_471_, v_____do__lift_76__boxed_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg(lean_object* v_inst_475_, lean_object* v_p_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v_toApplicative_478_; lean_object* v_toPure_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_toApplicative_478_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toApplicative_478_);
lean_dec(v_p_476_);
lean_dec_ref(v_inst_475_);
v_toPure_479_ = lean_ctor_get(v_toApplicative_478_, 1);
lean_inc(v_toPure_479_);
lean_dec_ref(v_toApplicative_478_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_apply_2(v_toPure_479_, lean_box(0), v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_toApplicative_482_; lean_object* v_toBind_483_; lean_object* v_toPure_484_; lean_object* v_head_485_; lean_object* v_tail_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_toApplicative_482_ = lean_ctor_get(v_inst_475_, 0);
v_toBind_483_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toBind_483_);
v_toPure_484_ = lean_ctor_get(v_toApplicative_482_, 1);
lean_inc(v_toPure_484_);
v_head_485_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_head_485_);
v_tail_486_ = lean_ctor_get(v_x_477_, 1);
lean_inc(v_tail_486_);
lean_dec_ref(v_x_477_);
lean_inc(v_head_485_);
lean_inc(v_p_476_);
v___f_487_ = lean_alloc_closure((void*)(l_List_findM_x3f___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_487_, 0, v_inst_475_);
lean_closure_set(v___f_487_, 1, v_p_476_);
lean_closure_set(v___f_487_, 2, v_tail_486_);
lean_closure_set(v___f_487_, 3, v_head_485_);
lean_closure_set(v___f_487_, 4, v_toPure_484_);
v___x_488_ = lean_apply_1(v_p_476_, v_head_485_);
v___x_489_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_488_, v___f_487_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___redArg___lam__0(lean_object* v_inst_490_, lean_object* v_p_491_, lean_object* v_tail_492_, lean_object* v_head_493_, lean_object* v_toPure_494_, uint8_t v_____do__lift_495_){
_start:
{
if (v_____do__lift_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v_toPure_494_);
lean_dec(v_head_493_);
v___x_496_ = l_List_findM_x3f___redArg(v_inst_490_, v_p_491_, v_tail_492_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_tail_492_);
lean_dec(v_p_491_);
lean_dec_ref(v_inst_490_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_head_493_);
v___x_498_ = lean_apply_2(v_toPure_494_, lean_box(0), v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f(lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_00_u03b1_501_, lean_object* v_p_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_List_findM_x3f___redArg(v_inst_500_, v_p_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(lean_object* v_x_505_, lean_object* v_h__1_506_, lean_object* v_h__2_507_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_507_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_apply_1(v_h__1_506_, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_head_510_; lean_object* v_tail_511_; lean_object* v___x_512_; 
lean_dec(v_h__1_506_);
v_head_510_ = lean_ctor_get(v_x_505_, 0);
lean_inc(v_head_510_);
v_tail_511_ = lean_ctor_get(v_x_505_, 1);
lean_inc(v_tail_511_);
lean_dec_ref(v_x_505_);
v___x_512_ = lean_apply_2(v_h__2_507_, v_head_510_, v_tail_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter(lean_object* v_00_u03b1_513_, lean_object* v_motive_514_, lean_object* v_x_515_, lean_object* v_h__1_516_, lean_object* v_h__2_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Init_Data_List_Control_0__List_findM_x3f_match__1_splitter___redArg(v_x_515_, v_h__1_516_, v_h__2_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(uint8_t v_____do__lift_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
if (v_____do__lift_519_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_520_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_h__2_521_, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_h__1_520_, v___x_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* v_____do__lift_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
uint8_t v_____do__lift_22__boxed_529_; lean_object* v_res_530_; 
v_____do__lift_22__boxed_529_ = lean_unbox(v_____do__lift_526_);
v_res_530_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_22__boxed_529_, v_h__1_527_, v_h__2_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(lean_object* v_motive_531_, uint8_t v_____do__lift_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___redArg(v_____do__lift_532_, v_h__1_533_, v_h__2_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter___boxed(lean_object* v_motive_536_, lean_object* v_____do__lift_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_){
_start:
{
uint8_t v_____do__lift_33__boxed_540_; lean_object* v_res_541_; 
v_____do__lift_33__boxed_540_ = lean_unbox(v_____do__lift_537_);
v_res_541_ = l___private_Init_Data_List_Control_0__List_anyM_match__1_splitter(v_motive_536_, v_____do__lift_33__boxed_540_, v_h__1_538_, v_h__2_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(uint8_t v_x_542_, lean_object* v_h__1_543_, lean_object* v_h__2_544_){
_start:
{
if (v_x_542_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_h__1_543_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_apply_1(v_h__2_544_, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_h__2_544_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_apply_1(v_h__1_543_, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_549_, lean_object* v_h__1_550_, lean_object* v_h__2_551_){
_start:
{
uint8_t v_x_22__boxed_552_; lean_object* v_res_553_; 
v_x_22__boxed_552_ = lean_unbox(v_x_549_);
v_res_553_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_552_, v_h__1_550_, v_h__2_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(lean_object* v_motive_554_, uint8_t v_x_555_, lean_object* v_h__1_556_, lean_object* v_h__2_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___redArg(v_x_555_, v_h__1_556_, v_h__2_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_h__1_561_, lean_object* v_h__2_562_){
_start:
{
uint8_t v_x_33__boxed_563_; lean_object* v_res_564_; 
v_x_33__boxed_563_ = lean_unbox(v_x_560_);
v_res_564_ = l___private_Init_Data_List_Control_0__List_filter_match__1_splitter(v_motive_559_, v_x_33__boxed_563_, v_h__1_561_, v_h__2_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg(lean_object* v_inst_565_, lean_object* v_f_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_toApplicative_568_; lean_object* v_toPure_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_toApplicative_568_ = lean_ctor_get(v_inst_565_, 0);
lean_inc_ref(v_toApplicative_568_);
lean_dec(v_f_566_);
lean_dec_ref(v_inst_565_);
v_toPure_569_ = lean_ctor_get(v_toApplicative_568_, 1);
lean_inc(v_toPure_569_);
lean_dec_ref(v_toApplicative_568_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_toApplicative_572_; lean_object* v_toBind_573_; lean_object* v_toPure_574_; lean_object* v_head_575_; lean_object* v_tail_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_toApplicative_572_ = lean_ctor_get(v_inst_565_, 0);
v_toBind_573_ = lean_ctor_get(v_inst_565_, 1);
lean_inc(v_toBind_573_);
v_toPure_574_ = lean_ctor_get(v_toApplicative_572_, 1);
lean_inc(v_toPure_574_);
v_head_575_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_575_);
v_tail_576_ = lean_ctor_get(v_x_567_, 1);
lean_inc(v_tail_576_);
lean_dec_ref(v_x_567_);
lean_inc(v_f_566_);
v___f_577_ = lean_alloc_closure((void*)(l_List_findSomeM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_577_, 0, v_inst_565_);
lean_closure_set(v___f_577_, 1, v_f_566_);
lean_closure_set(v___f_577_, 2, v_tail_576_);
lean_closure_set(v___f_577_, 3, v_toPure_574_);
v___x_578_ = lean_apply_1(v_f_566_, v_head_575_);
v___x_579_ = lean_apply_4(v_toBind_573_, lean_box(0), lean_box(0), v___x_578_, v___f_577_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___redArg___lam__0(lean_object* v_inst_580_, lean_object* v_f_581_, lean_object* v_tail_582_, lean_object* v_toPure_583_, lean_object* v_____do__lift_584_){
_start:
{
if (lean_obj_tag(v_____do__lift_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec(v_toPure_583_);
v___x_585_ = l_List_findSomeM_x3f___redArg(v_inst_580_, v_f_581_, v_tail_582_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; 
lean_dec(v_tail_582_);
lean_dec(v_f_581_);
lean_dec_ref(v_inst_580_);
v___x_586_ = lean_apply_2(v_toPure_583_, lean_box(0), v_____do__lift_584_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f(lean_object* v_m_587_, lean_object* v_inst_588_, lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_f_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_List_findSomeM_x3f___redArg(v_inst_588_, v_f_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(lean_object* v_x_594_, lean_object* v_h__1_595_, lean_object* v_h__2_596_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_h__2_596_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_apply_1(v_h__1_595_, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_601_; 
lean_dec(v_h__1_595_);
v_head_599_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_599_);
v_tail_600_ = lean_ctor_get(v_x_594_, 1);
lean_inc(v_tail_600_);
lean_dec_ref(v_x_594_);
v___x_601_ = lean_apply_2(v_h__2_596_, v_head_599_, v_tail_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter(lean_object* v_00_u03b1_602_, lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Init_Data_List_Control_0__List_mapA_match__1_splitter___redArg(v_x_604_, v_h__1_605_, v_h__2_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* v_____do__lift_608_, lean_object* v_h__1_609_, lean_object* v_h__2_610_){
_start:
{
if (lean_obj_tag(v_____do__lift_608_) == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec(v_h__1_609_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_apply_1(v_h__2_610_, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v_val_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_610_);
v_val_613_ = lean_ctor_get(v_____do__lift_608_, 0);
lean_inc(v_val_613_);
lean_dec_ref(v_____do__lift_608_);
v___x_614_ = lean_apply_1(v_h__1_609_, v_val_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter(lean_object* v_00_u03b2_615_, lean_object* v_motive_616_, lean_object* v_____do__lift_617_, lean_object* v_h__1_618_, lean_object* v_h__2_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l___private_Init_Data_List_Control_0__List_findSomeM_x3f_match__1_splitter___redArg(v_____do__lift_617_, v_h__1_618_, v_h__2_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_621_, lean_object* v_h__1_622_, lean_object* v_h__2_623_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_h__2_623_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_apply_1(v_h__1_622_, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; 
lean_dec(v_h__1_622_);
v_head_626_ = lean_ctor_get(v_x_621_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v_x_621_, 1);
lean_inc(v_tail_627_);
lean_dec_ref(v_x_621_);
v___x_628_ = lean_apply_2(v_h__2_623_, v_head_626_, v_tail_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_629_, lean_object* v_motive_630_, lean_object* v_x_631_, lean_object* v_h__1_632_, lean_object* v_h__2_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Init_Data_List_Control_0__List_getLast_x3f_match__1_splitter___redArg(v_x_631_, v_h__1_632_, v_h__2_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_h__1_636_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_1(v_h__2_637_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; 
lean_dec(v_h__2_637_);
v_val_640_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v_x_635_);
v___x_641_ = lean_apply_1(v_h__1_636_, v_val_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_642_, lean_object* v_motive_643_, lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Init_Data_List_Control_0__List_findSome_x3f_match__1_splitter___redArg(v_x_644_, v_h__1_645_, v_h__2_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg(lean_object* v_inst_648_, lean_object* v_f_649_, lean_object* v_as_x27_650_, lean_object* v_b_651_){
_start:
{
if (lean_obj_tag(v_as_x27_650_) == 0)
{
lean_object* v_toApplicative_652_; lean_object* v_toPure_653_; lean_object* v___x_654_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_648_, 0);
lean_inc_ref(v_toApplicative_652_);
lean_dec(v_f_649_);
lean_dec_ref(v_inst_648_);
v_toPure_653_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc(v_toPure_653_);
lean_dec_ref(v_toApplicative_652_);
v___x_654_ = lean_apply_2(v_toPure_653_, lean_box(0), v_b_651_);
return v___x_654_;
}
else
{
lean_object* v_toApplicative_655_; lean_object* v_toBind_656_; lean_object* v_toPure_657_; lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_toApplicative_655_ = lean_ctor_get(v_inst_648_, 0);
v_toBind_656_ = lean_ctor_get(v_inst_648_, 1);
lean_inc(v_toBind_656_);
v_toPure_657_ = lean_ctor_get(v_toApplicative_655_, 1);
lean_inc(v_toPure_657_);
v_head_658_ = lean_ctor_get(v_as_x27_650_, 0);
lean_inc(v_head_658_);
v_tail_659_ = lean_ctor_get(v_as_x27_650_, 1);
lean_inc(v_tail_659_);
lean_dec_ref(v_as_x27_650_);
lean_inc(v_f_649_);
v___f_660_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_660_, 0, v_toPure_657_);
lean_closure_set(v___f_660_, 1, v_inst_648_);
lean_closure_set(v___f_660_, 2, v_f_649_);
lean_closure_set(v___f_660_, 3, v_tail_659_);
v___x_661_ = lean_apply_3(v_f_649_, v_head_658_, lean_box(0), v_b_651_);
v___x_662_ = lean_apply_4(v_toBind_656_, lean_box(0), lean_box(0), v___x_661_, v___f_660_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___redArg___lam__0(lean_object* v_toPure_663_, lean_object* v_inst_664_, lean_object* v_f_665_, lean_object* v_tail_666_, lean_object* v_____do__lift_667_){
_start:
{
if (lean_obj_tag(v_____do__lift_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
lean_dec(v_tail_666_);
lean_dec(v_f_665_);
lean_dec_ref(v_inst_664_);
v_a_668_ = lean_ctor_get(v_____do__lift_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v_____do__lift_667_);
v___x_669_ = lean_apply_2(v_toPure_663_, lean_box(0), v_a_668_);
return v___x_669_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_671_; 
lean_dec(v_toPure_663_);
v_a_670_ = lean_ctor_get(v_____do__lift_667_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v_____do__lift_667_);
v___x_671_ = l_List_forIn_x27_loop___redArg(v_inst_664_, v_f_665_, v_tail_666_, v_a_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_m_674_, lean_object* v_inst_675_, lean_object* v_as_676_, lean_object* v_f_677_, lean_object* v_as_x27_678_, lean_object* v_b_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_List_forIn_x27_loop___redArg(v_inst_675_, v_f_677_, v_as_x27_678_, v_b_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___boxed(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_m_684_, lean_object* v_inst_685_, lean_object* v_as_686_, lean_object* v_f_687_, lean_object* v_as_x27_688_, lean_object* v_b_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_List_forIn_x27_loop(v_00_u03b1_682_, v_00_u03b2_683_, v_m_684_, v_inst_685_, v_as_686_, v_f_687_, v_as_x27_688_, v_b_689_, v_a_690_);
lean_dec(v_as_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27___redArg(lean_object* v_inst_692_, lean_object* v_as_693_, lean_object* v_init_694_, lean_object* v_f_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_List_forIn_x27_loop___redArg(v_inst_692_, v_f_695_, v_as_693_, v_init_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_m_699_, lean_object* v_inst_700_, lean_object* v_as_701_, lean_object* v_init_702_, lean_object* v_f_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_List_forIn_x27_loop___redArg(v_inst_700_, v_f_703_, v_as_701_, v_init_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_705_, lean_object* v_00_u03b2_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_List_forIn_x27_loop___redArg(v_inst_705_, v___y_709_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_711_){
_start:
{
lean_object* v___f_712_; 
v___f_712_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_712_, 0, v_inst_711_);
return v___f_712_;
}
}
LEAN_EXPORT lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_713_, lean_object* v_00_u03b1_714_, lean_object* v_inst_715_){
_start:
{
lean_object* v___f_716_; 
v___f_716_ = lean_alloc_closure((void*)(l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_716_, 0, v_inst_715_);
return v___f_716_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad___redArg(lean_object* v_inst_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, v_inst_717_);
lean_closure_set(v___x_718_, 2, lean_box(0));
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_List_instForMOfMonad(lean_object* v_m_719_, lean_object* v_00_u03b1_720_, lean_object* v_inst_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_closure((void*)(l_List_forM), 5, 3);
lean_closure_set(v___x_722_, 0, lean_box(0));
lean_closure_set(v___x_722_, 1, v_inst_721_);
lean_closure_set(v___x_722_, 2, lean_box(0));
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_List_instFunctor___lam__0(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(v___x_727_, 0, lean_box(0));
lean_closure_set(v___x_727_, 1, lean_box(0));
lean_closure_set(v___x_727_, 2, v___y_725_);
v___x_728_ = lean_box(0);
v___x_729_ = l_List_mapTR_loop___redArg(v___x_727_, v___y_726_, v___x_728_);
return v___x_729_;
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
