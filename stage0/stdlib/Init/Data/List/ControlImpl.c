// Lean compiler output
// Module: Init.Data.List.ControlImpl
// Imports: public import Init.Data.List.Control public import Init.Data.List.Impl
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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_flatMapMTR_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_flatMapMTR_loop___redArg___closed__0 = (const lean_object*)&l_List_flatMapMTR_loop___redArg___closed__0_value;
static const lean_array_object l_List_flatMapMTR_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_flatMapMTR_loop___redArg___closed__1 = (const lean_object*)&l_List_flatMapMTR_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapMTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapMTR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop___redArg(lean_object* v_inst_4_, lean_object* v_f_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v_toApplicative_8_; lean_object* v_toPure_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_toApplicative_8_ = lean_ctor_get(v_inst_4_, 0);
lean_inc_ref(v_toApplicative_8_);
lean_dec(v_f_5_);
lean_dec_ref(v_inst_4_);
v_toPure_9_ = lean_ctor_get(v_toApplicative_8_, 1);
lean_inc(v_toPure_9_);
lean_dec_ref(v_toApplicative_8_);
v___x_10_ = l_List_reverse___redArg(v_x_7_);
v___x_11_ = ((lean_object*)(l_List_flatMapMTR_loop___redArg___closed__0));
v___x_12_ = ((lean_object*)(l_List_flatMapMTR_loop___redArg___closed__1));
v___x_13_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_11_, v___x_10_, v___x_12_);
v___x_14_ = lean_apply_2(v_toPure_9_, lean_box(0), v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_toBind_15_; lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_toBind_15_ = lean_ctor_get(v_inst_4_, 1);
lean_inc(v_toBind_15_);
v_head_16_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_tail_17_);
lean_dec_ref(v_x_6_);
lean_inc(v_f_5_);
v___f_18_ = lean_alloc_closure((void*)(l_List_flatMapMTR_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_18_, 0, v_x_7_);
lean_closure_set(v___f_18_, 1, v_inst_4_);
lean_closure_set(v___f_18_, 2, v_f_5_);
lean_closure_set(v___f_18_, 3, v_tail_17_);
v___x_19_ = lean_apply_1(v_f_5_, v_head_16_);
v___x_20_ = lean_apply_4(v_toBind_15_, lean_box(0), lean_box(0), v___x_19_, v___f_18_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop___redArg___lam__0(lean_object* v_x_21_, lean_object* v_inst_22_, lean_object* v_f_23_, lean_object* v_tail_24_, lean_object* v_bs_x27_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v_bs_x27_25_);
lean_ctor_set(v___x_26_, 1, v_x_21_);
v___x_27_ = l_List_flatMapMTR_loop___redArg(v_inst_22_, v_f_23_, v_tail_24_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapMTR_loop(lean_object* v_m_28_, lean_object* v_inst_29_, lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_f_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_List_flatMapMTR_loop___redArg(v_inst_29_, v_f_32_, v_x_33_, v_x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapMTR___redArg(lean_object* v_inst_36_, lean_object* v_f_37_, lean_object* v_as_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_box(0);
v___x_40_ = l_List_flatMapMTR_loop___redArg(v_inst_36_, v_f_37_, v_as_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapMTR(lean_object* v_m_41_, lean_object* v_inst_42_, lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_f_45_, lean_object* v_as_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(0);
v___x_48_ = l_List_flatMapMTR_loop___redArg(v_inst_42_, v_f_45_, v_as_46_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_h__2_52_);
v___x_53_ = lean_apply_1(v_h__1_51_, v_x_50_);
return v___x_53_;
}
else
{
lean_object* v_head_54_; lean_object* v_tail_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_51_);
v_head_54_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_head_54_);
v_tail_55_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_tail_55_);
lean_dec_ref(v_x_49_);
v___x_56_ = lean_apply_3(v_h__2_52_, v_head_54_, v_tail_55_, v_x_50_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_64_; 
lean_dec(v_h__2_63_);
v___x_64_ = lean_apply_1(v_h__1_62_, v_x_61_);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_62_);
v_head_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_65_);
v_tail_66_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_tail_66_);
lean_dec_ref(v_x_60_);
v___x_67_ = lean_apply_3(v_h__2_63_, v_head_65_, v_tail_66_, v_x_61_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_72_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_apply_1(v_h__1_70_, v_x_69_);
return v___x_72_;
}
else
{
lean_object* v_head_73_; lean_object* v_tail_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_70_);
v_head_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_head_73_);
v_tail_74_ = lean_ctor_get(v_x_68_, 1);
lean_inc(v_tail_74_);
lean_dec_ref(v_x_68_);
v___x_75_ = lean_apply_3(v_h__2_71_, v_head_73_, v_tail_74_, v_x_69_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_83_; 
lean_dec(v_h__2_82_);
v___x_83_ = lean_apply_1(v_h__1_81_, v_x_80_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_86_; 
lean_dec(v_h__1_81_);
v_head_84_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_head_84_);
v_tail_85_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_tail_85_);
lean_dec_ref(v_x_79_);
v___x_86_ = lean_apply_3(v_h__2_82_, v_head_84_, v_tail_85_, v_x_80_);
return v___x_86_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_ControlImpl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_ControlImpl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_ControlImpl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ControlImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_ControlImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_ControlImpl(builtin);
}
#ifdef __cplusplus
}
#endif
