// Lean compiler output
// Module: Init.Data.Option.Attach
// Imports: public import Init.Data.Array.Attach public import Init.Data.Option.Lemmas import Init.Data.Bool import Init.Data.Option.Array import Init.Data.Option.List import Init.Data.Subtype.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_filterM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_filterM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Option_instMonadAttach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_instMonadAttach___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_instMonadAttach___closed__0 = (const lean_object*)&l_Option_instMonadAttach___closed__0_value;
LEAN_EXPORT const lean_object* l_Option_instMonadAttach = (const lean_object*)&l_Option_instMonadAttach___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object* v_o_1_){
_start:
{
lean_inc(v_o_1_);
return v_o_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object* v_o_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(v_o_2_);
lean_dec(v_o_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object* v_00_u03b1_4_, lean_object* v_o_5_, lean_object* v_P_6_, lean_object* v_x_7_){
_start:
{
lean_inc(v_o_5_);
return v_o_5_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_o_9_, lean_object* v_P_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(v_00_u03b1_8_, v_o_9_, v_P_10_, v_x_11_);
lean_dec(v_o_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object* v_xs_13_){
_start:
{
lean_inc(v_xs_13_);
return v_xs_13_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object* v_xs_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Option_attach___redArg(v_xs_14_);
lean_dec(v_xs_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Option_attach(lean_object* v_00_u03b1_16_, lean_object* v_xs_17_){
_start:
{
lean_inc(v_xs_17_);
return v_xs_17_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object* v_00_u03b1_18_, lean_object* v_xs_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Option_attach(v_00_u03b1_18_, v_xs_19_);
lean_dec(v_xs_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter___redArg(lean_object* v_b_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_b_21_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_23_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__1_22_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_22_);
v_val_26_ = lean_ctor_get(v_b_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v_b_21_, 1);
v___x_27_ = lean_apply_1(v_h__2_23_, v_val_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_b_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_b_30_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_32_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__1_31_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_val_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_31_);
v_val_35_ = lean_ctor_get(v_b_30_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v_b_30_, 1);
v___x_36_ = lean_apply_1(v_h__2_32_, v_val_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object* v_o_37_){
_start:
{
if (lean_obj_tag(v_o_37_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
else
{
lean_object* v_val_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_val_39_ = lean_ctor_get(v_o_37_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v_o_37_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v_o_37_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_val_39_);
lean_dec(v_o_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_val_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_unattach(lean_object* v_00_u03b1_47_, lean_object* v_p_48_, lean_object* v_o_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Option_unattach___redArg(v_o_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_filterM_match__1_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_53_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__1_52_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_val_56_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v_x_51_, 1);
v___x_57_ = lean_apply_1(v_h__2_53_, v_val_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_filterM_match__1_splitter(lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_62_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_apply_1(v_h__1_61_, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_61_);
v_val_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v_x_60_, 1);
v___x_66_ = lean_apply_1(v_h__2_62_, v_val_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0(lean_object* v_00_u03b1_67_, lean_object* v_x_68_){
_start:
{
lean_inc(v_x_68_);
return v_x_68_;
}
}
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Option_instMonadAttach___lam__0(v_00_u03b1_69_, v_x_70_);
lean_dec(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v___x_77_; 
lean_dec(v_h__1_75_);
v___x_77_ = lean_apply_1(v_h__2_76_, lean_box(0));
return v___x_77_;
}
else
{
lean_object* v_val_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_76_);
v_val_78_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_x_74_, 1);
v___x_79_ = lean_apply_2(v_h__1_75_, v_val_78_, lean_box(0));
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(lean_object* v_m_80_, lean_object* v_inst_81_, lean_object* v_00_u03b1_82_, lean_object* v_x_83_, lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_88_; 
lean_dec(v_h__1_86_);
v___x_88_ = lean_apply_1(v_h__2_87_, lean_box(0));
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_87_);
v_val_89_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_x_85_, 1);
v___x_90_ = lean_apply_2(v_h__1_86_, v_val_89_, lean_box(0));
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(lean_object* v_m_91_, lean_object* v_inst_92_, lean_object* v_00_u03b1_93_, lean_object* v_x_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(v_m_91_, v_inst_92_, v_00_u03b1_93_, v_x_94_, v_motive_95_, v_x_96_, v_h__1_97_, v_h__2_98_);
lean_dec(v_x_94_);
lean_dec(v_inst_92_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
if (lean_obj_tag(v_____do__lift_100_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_101_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__2_102_, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; 
lean_dec(v_h__2_102_);
v_val_105_ = lean_ctor_get(v_____do__lift_100_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v_____do__lift_100_, 1);
v___x_106_ = lean_apply_1(v_h__1_101_, v_val_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_107_, lean_object* v_motive_108_, lean_object* v_____do__lift_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (lean_obj_tag(v_____do__lift_109_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_110_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__2_111_, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_111_);
v_val_114_ = lean_ctor_get(v_____do__lift_109_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v_____do__lift_109_, 1);
v___x_115_ = lean_apply_1(v_h__1_110_, v_val_114_);
return v___x_115_;
}
}
}
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
