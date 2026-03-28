// Lean compiler output
// Module: Lake.Config.MetaClasses
// Imports: public import Lean.Data.NameMap.Basic
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
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault___redArg(lean_object* v_field_1_, lean_object* v_cfg_2_){
_start:
{
lean_object* v_mkDefault_3_; lean_object* v___x_4_; 
v_mkDefault_3_ = lean_ctor_get(v_field_1_, 3);
lean_inc(v_mkDefault_3_);
lean_dec_ref(v_field_1_);
v___x_4_ = lean_apply_1(v_mkDefault_3_, v_cfg_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault(lean_object* v_00_u03c3_5_, lean_object* v_00_u03b1_6_, lean_object* v_name_7_, lean_object* v_field_8_, lean_object* v_cfg_9_){
_start:
{
lean_object* v_mkDefault_10_; lean_object* v___x_11_; 
v_mkDefault_10_ = lean_ctor_get(v_field_8_, 3);
lean_inc(v_mkDefault_10_);
lean_dec_ref(v_field_8_);
v___x_11_ = lean_apply_1(v_mkDefault_10_, v_cfg_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFieldDefault___boxed(lean_object* v_00_u03c3_12_, lean_object* v_00_u03b1_13_, lean_object* v_name_14_, lean_object* v_field_15_, lean_object* v_cfg_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lake_mkFieldDefault(v_00_u03c3_12_, v_00_u03b1_13_, v_name_14_, v_field_15_, v_cfg_16_);
lean_dec(v_name_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__0(lean_object* v_field_18_, lean_object* v_parent_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_get_21_; lean_object* v_get_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_get_21_ = lean_ctor_get(v_field_18_, 0);
lean_inc(v_get_21_);
lean_dec_ref(v_field_18_);
v_get_22_ = lean_ctor_get(v_parent_19_, 0);
lean_inc(v_get_22_);
lean_dec_ref(v_parent_19_);
v___x_23_ = lean_apply_1(v_get_22_, v_s_20_);
v___x_24_ = lean_apply_1(v_get_21_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__1(lean_object* v_parent_25_, lean_object* v_field_26_, lean_object* v_a_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_modify_29_; lean_object* v_set_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_modify_29_ = lean_ctor_get(v_parent_25_, 2);
lean_inc(v_modify_29_);
lean_dec_ref(v_parent_25_);
v_set_30_ = lean_ctor_get(v_field_26_, 1);
lean_inc(v_set_30_);
lean_dec_ref(v_field_26_);
v___x_31_ = lean_apply_1(v_set_30_, v_a_27_);
v___x_32_ = lean_apply_2(v_modify_29_, v___x_31_, v___y_28_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__2(lean_object* v_parent_33_, lean_object* v_field_34_, lean_object* v_f_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_modify_37_; lean_object* v_modify_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_modify_37_ = lean_ctor_get(v_parent_33_, 2);
lean_inc(v_modify_37_);
lean_dec_ref(v_parent_33_);
v_modify_38_ = lean_ctor_get(v_field_34_, 2);
lean_inc(v_modify_38_);
lean_dec_ref(v_field_34_);
v___x_39_ = lean_apply_1(v_modify_38_, v_f_35_);
v___x_40_ = lean_apply_2(v_modify_37_, v___x_39_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg___lam__3(lean_object* v_field_41_, lean_object* v_parent_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_mkDefault_44_; lean_object* v_get_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_mkDefault_44_ = lean_ctor_get(v_field_41_, 3);
lean_inc(v_mkDefault_44_);
lean_dec_ref(v_field_41_);
v_get_45_ = lean_ctor_get(v_parent_42_, 0);
lean_inc(v_get_45_);
lean_dec_ref(v_parent_42_);
v___x_46_ = lean_apply_1(v_get_45_, v_s_43_);
v___x_47_ = lean_apply_1(v_mkDefault_44_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___redArg(lean_object* v_parent_48_, lean_object* v_field_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
lean_inc_ref_n(v_parent_48_, 3);
lean_inc_ref_n(v_field_49_, 3);
v___f_50_ = lean_alloc_closure((void*)(l_Lake_instConfigFieldOfConfigParent___redArg___lam__0), 3, 2);
lean_closure_set(v___f_50_, 0, v_field_49_);
lean_closure_set(v___f_50_, 1, v_parent_48_);
v___f_51_ = lean_alloc_closure((void*)(l_Lake_instConfigFieldOfConfigParent___redArg___lam__1), 4, 2);
lean_closure_set(v___f_51_, 0, v_parent_48_);
lean_closure_set(v___f_51_, 1, v_field_49_);
v___f_52_ = lean_alloc_closure((void*)(l_Lake_instConfigFieldOfConfigParent___redArg___lam__2), 4, 2);
lean_closure_set(v___f_52_, 0, v_parent_48_);
lean_closure_set(v___f_52_, 1, v_field_49_);
v___f_53_ = lean_alloc_closure((void*)(l_Lake_instConfigFieldOfConfigParent___redArg___lam__3), 3, 2);
lean_closure_set(v___f_53_, 0, v_field_49_);
lean_closure_set(v___f_53_, 1, v_parent_48_);
v___x_54_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_54_, 0, v___f_50_);
lean_ctor_set(v___x_54_, 1, v___f_51_);
lean_ctor_set(v___x_54_, 2, v___f_52_);
lean_ctor_set(v___x_54_, 3, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent(lean_object* v_00_u03c3_55_, lean_object* v_00_u03c1_56_, lean_object* v_name_57_, lean_object* v_00_u03b1_58_, lean_object* v_parent_59_, lean_object* v_field_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lake_instConfigFieldOfConfigParent___redArg(v_parent_59_, v_field_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_instConfigFieldOfConfigParent___boxed(lean_object* v_00_u03c3_62_, lean_object* v_00_u03c1_63_, lean_object* v_name_64_, lean_object* v_00_u03b1_65_, lean_object* v_parent_66_, lean_object* v_field_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lake_instConfigFieldOfConfigParent(v_00_u03c3_62_, v_00_u03c1_63_, v_name_64_, v_00_u03b1_65_, v_parent_66_, v_field_67_);
lean_dec(v_name_64_);
return v_res_68_;
}
}
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_MetaClasses(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_MetaClasses(builtin);
}
#ifdef __cplusplus
}
#endif
