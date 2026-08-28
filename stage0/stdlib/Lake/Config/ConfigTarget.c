// Lean compiler output
// Module: Lake.Config.ConfigTarget
// Imports: public import Lake.Config.Package
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instHashableConfigTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instHashableConfigTarget___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instHashableConfigTarget___closed__0 = (const lean_object*)&l_Lake_instHashableConfigTarget___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instBEqConfigTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instBEqConfigTarget___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instBEqConfigTarget___closed__0 = (const lean_object*)&l_Lake_instBEqConfigTarget___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_configTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_configTargets___closed__0 = (const lean_object*)&l_Lake_Package_configTargets___closed__0_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__1 = (const lean_object*)&l_Lake_Package_configTargets___closed__1_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__2 = (const lean_object*)&l_Lake_Package_configTargets___closed__2_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__3 = (const lean_object*)&l_Lake_Package_configTargets___closed__3_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__4 = (const lean_object*)&l_Lake_Package_configTargets___closed__4_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__5 = (const lean_object*)&l_Lake_Package_configTargets___closed__5_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__6 = (const lean_object*)&l_Lake_Package_configTargets___closed__6_value;
static const lean_closure_object l_Lake_Package_configTargets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_configTargets___closed__7 = (const lean_object*)&l_Lake_Package_configTargets___closed__7_value;
static const lean_ctor_object l_Lake_Package_configTargets___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_configTargets___closed__1_value),((lean_object*)&l_Lake_Package_configTargets___closed__2_value)}};
static const lean_object* l_Lake_Package_configTargets___closed__8 = (const lean_object*)&l_Lake_Package_configTargets___closed__8_value;
static const lean_ctor_object l_Lake_Package_configTargets___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_configTargets___closed__8_value),((lean_object*)&l_Lake_Package_configTargets___closed__3_value),((lean_object*)&l_Lake_Package_configTargets___closed__4_value),((lean_object*)&l_Lake_Package_configTargets___closed__5_value),((lean_object*)&l_Lake_Package_configTargets___closed__6_value)}};
static const lean_object* l_Lake_Package_configTargets___closed__9 = (const lean_object*)&l_Lake_Package_configTargets___closed__9_value;
static const lean_ctor_object l_Lake_Package_configTargets___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_configTargets___closed__9_value),((lean_object*)&l_Lake_Package_configTargets___closed__7_value)}};
static const lean_object* l_Lake_Package_configTargets___closed__10 = (const lean_object*)&l_Lake_Package_configTargets___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashableConfigTarget___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v_name_2_; 
v_name_2_ = lean_ctor_get(v_x_1_, 1);
if (lean_obj_tag(v_name_2_) == 0)
{
uint64_t v___x_3_; 
v___x_3_ = 1723ULL;
return v___x_3_;
}
else
{
uint64_t v_hash_4_; 
v_hash_4_ = lean_ctor_get_uint64(v_name_2_, sizeof(void*)*2);
return v_hash_4_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___lam__0___boxed(lean_object* v_x_5_){
_start:
{
uint64_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lake_instHashableConfigTarget___lam__0(v_x_5_);
lean_dec_ref(v_x_5_);
v_r_7_ = lean_box_uint64(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget(lean_object* v_k_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l_Lake_instHashableConfigTarget___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableConfigTarget___boxed(lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lake_instHashableConfigTarget(v_k_11_);
lean_dec(v_k_11_);
return v_res_12_;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqConfigTarget___lam__0(lean_object* v_x1_13_, lean_object* v_x2_14_){
_start:
{
lean_object* v_name_15_; lean_object* v_name_16_; uint8_t v___x_17_; 
v_name_15_ = lean_ctor_get(v_x1_13_, 1);
v_name_16_ = lean_ctor_get(v_x2_14_, 1);
v___x_17_ = lean_name_eq(v_name_15_, v_name_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___lam__0___boxed(lean_object* v_x1_18_, lean_object* v_x2_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Lake_instBEqConfigTarget___lam__0(v_x1_18_, v_x2_19_);
lean_dec_ref(v_x2_19_);
lean_dec_ref(v_x1_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget(lean_object* v_k_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = ((lean_object*)(l_Lake_instBEqConfigTarget___closed__0));
return v___f_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqConfigTarget___boxed(lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_instBEqConfigTarget(v_k_25_);
lean_dec(v_k_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget(lean_object* v_pkg_27_, lean_object* v_self_28_){
_start:
{
lean_object* v_name_29_; lean_object* v_config_30_; lean_object* v___x_31_; 
v_name_29_ = lean_ctor_get(v_self_28_, 1);
v_config_30_ = lean_ctor_get(v_self_28_, 3);
lean_inc(v_config_30_);
lean_inc(v_name_29_);
v___x_31_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_31_, 0, v_pkg_27_);
lean_ctor_set(v___x_31_, 1, v_name_29_);
lean_ctor_set(v___x_31_, 2, v_config_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_mkConfigTarget___boxed(lean_object* v_pkg_32_, lean_object* v_self_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_PConfigDecl_mkConfigTarget(v_pkg_32_, v_self_33_);
lean_dec_ref(v_self_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0(lean_object* v_kind_35_, lean_object* v_self_36_, lean_object* v_x1_37_, lean_object* v_x2_38_){
_start:
{
lean_object* v_name_39_; lean_object* v_kind_40_; lean_object* v_config_41_; uint8_t v___x_42_; 
v_name_39_ = lean_ctor_get(v_x2_38_, 1);
v_kind_40_ = lean_ctor_get(v_x2_38_, 2);
v_config_41_ = lean_ctor_get(v_x2_38_, 3);
v___x_42_ = lean_name_eq(v_kind_40_, v_kind_35_);
if (v___x_42_ == 0)
{
lean_dec_ref(v_self_36_);
return v_x1_37_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_config_41_);
lean_inc(v_name_39_);
v___x_43_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_43_, 0, v_self_36_);
lean_ctor_set(v___x_43_, 1, v_name_39_);
lean_ctor_set(v___x_43_, 2, v_config_41_);
v___x_44_ = lean_array_push(v_x1_37_, v___x_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets___lam__0___boxed(lean_object* v_kind_45_, lean_object* v_self_46_, lean_object* v_x1_47_, lean_object* v_x2_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lake_Package_configTargets___lam__0(v_kind_45_, v_self_46_, v_x1_47_, v_x2_48_);
lean_dec_ref(v_x2_48_);
lean_dec(v_kind_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configTargets(lean_object* v_kind_71_, lean_object* v_self_72_){
_start:
{
lean_object* v_targetDecls_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_targetDecls_73_ = lean_ctor_get(v_self_72_, 15);
lean_inc_ref(v_targetDecls_73_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = ((lean_object*)(l_Lake_Package_configTargets___closed__0));
v___x_76_ = lean_array_get_size(v_targetDecls_73_);
v___x_77_ = ((lean_object*)(l_Lake_Package_configTargets___closed__10));
v___x_78_ = lean_nat_dec_lt(v___x_74_, v___x_76_);
if (v___x_78_ == 0)
{
lean_dec_ref(v_targetDecls_73_);
lean_dec_ref(v_self_72_);
lean_dec(v_kind_71_);
return v___x_75_;
}
else
{
lean_object* v___f_79_; uint8_t v___x_80_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lake_Package_configTargets___lam__0___boxed), 4, 2);
lean_closure_set(v___f_79_, 0, v_kind_71_);
lean_closure_set(v___f_79_, 1, v_self_72_);
v___x_80_ = lean_nat_dec_le(v___x_76_, v___x_76_);
if (v___x_80_ == 0)
{
if (v___x_78_ == 0)
{
lean_dec_ref(v___f_79_);
lean_dec_ref(v_targetDecls_73_);
return v___x_75_;
}
else
{
size_t v___x_81_; size_t v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((size_t)0ULL);
v___x_82_ = lean_usize_of_nat(v___x_76_);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_77_, v___f_79_, v_targetDecls_73_, v___x_81_, v___x_82_, v___x_75_);
return v___x_83_;
}
}
else
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((size_t)0ULL);
v___x_85_ = lean_usize_of_nat(v___x_76_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_77_, v___f_79_, v_targetDecls_73_, v___x_84_, v___x_85_, v___x_75_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f(lean_object* v_kind_87_, lean_object* v_name_88_, lean_object* v_self_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lake_Package_findTargetDecl_x3f(v_name_88_, v_self_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec_ref(v_self_89_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_105_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_105_ == 0)
{
v___x_94_ = v___x_90_;
v_isShared_95_ = v_isSharedCheck_105_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v___x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_105_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_name_96_; lean_object* v_kind_97_; lean_object* v_config_98_; uint8_t v___x_99_; 
v_name_96_ = lean_ctor_get(v_val_92_, 1);
lean_inc(v_name_96_);
v_kind_97_ = lean_ctor_get(v_val_92_, 2);
lean_inc(v_kind_97_);
v_config_98_ = lean_ctor_get(v_val_92_, 3);
lean_inc(v_config_98_);
lean_dec(v_val_92_);
v___x_99_ = lean_name_eq(v_kind_97_, v_kind_87_);
lean_dec(v_kind_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_config_98_);
lean_dec(v_name_96_);
lean_del_object(v___x_94_);
lean_dec_ref(v_self_89_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v_self_89_);
lean_ctor_set(v___x_101_, 1, v_name_96_);
lean_ctor_set(v___x_101_, 2, v_config_98_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_101_);
v___x_103_ = v___x_94_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findConfigTarget_x3f___boxed(lean_object* v_kind_106_, lean_object* v_name_107_, lean_object* v_self_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lake_Package_findConfigTarget_x3f(v_kind_106_, v_name_107_, v_self_108_);
lean_dec(v_name_107_);
lean_dec(v_kind_106_);
return v_res_109_;
}
}
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_ConfigTarget(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_ConfigTarget(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_ConfigTarget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_ConfigTarget(builtin);
}
#ifdef __cplusplus
}
#endif
