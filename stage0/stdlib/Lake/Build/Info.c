// Lean compiler output
// Module: Lake.Build.Info
// Imports: public import Lake.Config.Package meta import all Lake.Build.Data
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
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_key(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_targetKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_targetKey___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_key(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringBuildInfo___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToStringBuildInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToStringBuildInfo___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToStringBuildInfo___closed__0 = (const lean_object*)&l_Lake_instToStringBuildInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringBuildInfo = (const lean_object*)&l_Lake_instToStringBuildInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_BuildInfo_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_package_7_; lean_object* v_target_8_; lean_object* v___x_9_; 
v_package_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_package_7_);
v_target_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_target_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_package_7_, v_target_8_);
return v___x_9_;
}
else
{
lean_object* v_target_10_; lean_object* v_kind_11_; lean_object* v_data_12_; lean_object* v_facet_13_; lean_object* v___x_14_; 
v_target_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_target_10_);
v_kind_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_kind_11_);
v_data_12_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_data_12_);
v_facet_13_ = lean_ctor_get(v_t_5_, 3);
lean_inc(v_facet_13_);
lean_dec_ref_known(v_t_5_, 4);
v___x_14_ = lean_apply_4(v_k_6_, v_target_10_, v_kind_11_, v_data_12_, v_facet_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_BuildInfo_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim___redArg(lean_object* v_t_27_, lean_object* v_target_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_27_, v_target_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_target_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_31_, v_target_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim___redArg(lean_object* v_t_35_, lean_object* v_facet_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_35_, v_facet_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_facet_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_39_, v_facet_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_key(lean_object* v_self_43_){
_start:
{
lean_object* v_keyName_44_; lean_object* v___x_45_; 
v_keyName_44_ = lean_ctor_get(v_self_43_, 2);
lean_inc(v_keyName_44_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v_keyName_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_key___boxed(lean_object* v_self_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lake_Package_key(v_self_46_);
lean_dec_ref(v_self_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_targetKey(lean_object* v_target_48_, lean_object* v_self_49_){
_start:
{
lean_object* v_keyName_50_; lean_object* v___x_51_; 
v_keyName_50_ = lean_ctor_get(v_self_49_, 2);
lean_inc(v_keyName_50_);
v___x_51_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_51_, 0, v_keyName_50_);
lean_ctor_set(v___x_51_, 1, v_target_48_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_targetKey___boxed(lean_object* v_target_52_, lean_object* v_self_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_Package_targetKey(v_target_52_, v_self_53_);
lean_dec_ref(v_self_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_key(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_package_56_; lean_object* v_target_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_65_; 
v_package_56_ = lean_ctor_get(v_x_55_, 0);
v_target_57_ = lean_ctor_get(v_x_55_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_65_ == 0)
{
v___x_59_ = v_x_55_;
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_target_57_);
lean_inc(v_package_56_);
lean_dec(v_x_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_keyName_61_; lean_object* v___x_63_; 
v_keyName_61_ = lean_ctor_get(v_package_56_, 2);
lean_inc(v_keyName_61_);
lean_dec_ref(v_package_56_);
if (v_isShared_60_ == 0)
{
lean_ctor_set_tag(v___x_59_, 3);
lean_ctor_set(v___x_59_, 0, v_keyName_61_);
v___x_63_ = v___x_59_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_keyName_61_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_target_57_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
else
{
lean_object* v_target_66_; lean_object* v_facet_67_; lean_object* v___x_68_; 
v_target_66_ = lean_ctor_get(v_x_55_, 0);
lean_inc_ref(v_target_66_);
v_facet_67_ = lean_ctor_get(v_x_55_, 3);
lean_inc(v_facet_67_);
lean_dec_ref_known(v_x_55_, 4);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v_target_66_);
lean_ctor_set(v___x_68_, 1, v_facet_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringBuildInfo___lam__0(lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l_Lake_BuildInfo_key(v_x_69_);
v___x_71_ = l_Lake_BuildKey_toString(v___x_70_);
return v___x_71_;
}
}
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Info(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Info(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Info(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Info(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Info(builtin);
}
#ifdef __cplusplus
}
#endif
