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
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lake_BuildInfo_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_package_8_; lean_object* v_target_9_; lean_object* v___x_10_; 
v_package_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_package_8_);
v_target_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_target_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_package_8_, v_target_9_);
return v___x_10_;
}
else
{
lean_object* v_target_11_; lean_object* v_kind_12_; lean_object* v_data_13_; lean_object* v_facet_14_; lean_object* v___x_15_; 
v_target_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_target_11_);
v_kind_12_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_kind_12_);
v_data_13_ = lean_ctor_get(v_t_6_, 2);
lean_inc(v_data_13_);
v_facet_14_ = lean_ctor_get(v_t_6_, 3);
lean_inc(v_facet_14_);
lean_dec_ref(v_t_6_);
v___x_15_ = lean_apply_4(v_k_7_, v_target_11_, v_kind_12_, v_data_13_, v_facet_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lake_BuildInfo_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim___redArg(lean_object* v_t_28_, lean_object* v_target_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_28_, v_target_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_target_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_target_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_32_, v_target_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim___redArg(lean_object* v_t_36_, lean_object* v_facet_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_36_, v_facet_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_facet_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_facet_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_BuildInfo_ctorElim___redArg(v_t_40_, v_facet_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_key(lean_object* v_self_44_){
_start:
{
lean_object* v_keyName_45_; lean_object* v___x_46_; 
v_keyName_45_ = lean_ctor_get(v_self_44_, 2);
lean_inc(v_keyName_45_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v_keyName_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_key___boxed(lean_object* v_self_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_Package_key(v_self_47_);
lean_dec_ref(v_self_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_targetKey(lean_object* v_target_49_, lean_object* v_self_50_){
_start:
{
lean_object* v_keyName_51_; lean_object* v___x_52_; 
v_keyName_51_ = lean_ctor_get(v_self_50_, 2);
lean_inc(v_keyName_51_);
v___x_52_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_52_, 0, v_keyName_51_);
lean_ctor_set(v___x_52_, 1, v_target_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_targetKey___boxed(lean_object* v_target_53_, lean_object* v_self_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lake_Package_targetKey(v_target_53_, v_self_54_);
lean_dec_ref(v_self_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_key(lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v_package_57_; lean_object* v_target_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_66_; 
v_package_57_ = lean_ctor_get(v_x_56_, 0);
v_target_58_ = lean_ctor_get(v_x_56_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_66_ == 0)
{
v___x_60_ = v_x_56_;
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_target_58_);
lean_inc(v_package_57_);
lean_dec(v_x_56_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_keyName_62_; lean_object* v___x_64_; 
v_keyName_62_ = lean_ctor_get(v_package_57_, 2);
lean_inc(v_keyName_62_);
lean_dec_ref(v_package_57_);
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 3);
lean_ctor_set(v___x_60_, 0, v_keyName_62_);
v___x_64_ = v___x_60_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_keyName_62_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_target_58_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
else
{
lean_object* v_target_67_; lean_object* v_facet_68_; lean_object* v___x_69_; 
v_target_67_ = lean_ctor_get(v_x_56_, 0);
lean_inc_ref(v_target_67_);
v_facet_68_ = lean_ctor_get(v_x_56_, 3);
lean_inc(v_facet_68_);
lean_dec_ref(v_x_56_);
v___x_69_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_69_, 0, v_target_67_);
lean_ctor_set(v___x_69_, 1, v_facet_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringBuildInfo___lam__0(lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = l_Lake_BuildInfo_key(v_x_70_);
v___x_72_ = l_Lake_BuildKey_toString(v___x_71_);
return v___x_72_;
}
}
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Info(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
