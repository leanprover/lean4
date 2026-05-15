// Lean compiler output
// Module: Lean.Elab.RecAppSyntax
// Imports: public import Lean.Expr
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_recApp"};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 14, 43, 140, 165, 123, 61, 74)}};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
static const lean_string_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_recAppPos"};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 195, 249, 168, 89, 177, 245, 31)}};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object* v_e_9_, lean_object* v_stx_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_m_14_; uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_11_ = l_Lean_KVMap_empty;
v___x_12_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
lean_inc(v_stx_10_);
v___x_13_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_13_, 0, v_stx_10_);
v_m_14_ = l_Lean_KVMap_insert(v___x_11_, v___x_12_, v___x_13_);
v___x_15_ = 0;
v___x_16_ = l_Lean_Syntax_getPos_x3f(v_stx_10_, v___x_15_);
lean_dec(v_stx_10_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_mkMData(v_m_14_, v_e_9_);
return v___x_17_;
}
else
{
lean_object* v_val_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_28_; 
v_val_18_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_28_ == 0)
{
v___x_20_ = v___x_16_;
v_isShared_21_ = v_isSharedCheck_28_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_val_18_);
lean_dec(v___x_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_28_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppPosKey));
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 3);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_val_18_);
v___x_24_ = v_reuseFailAlloc_27_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = l_Lean_KVMap_insert(v_m_14_, v___x_22_, v___x_24_);
v___x_26_ = l_Lean_mkMData(v___x_25_, v_e_9_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object* v_e_29_){
_start:
{
if (lean_obj_tag(v_e_29_) == 10)
{
lean_object* v_data_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_data_30_ = lean_ctor_get(v_e_29_, 0);
v___x_31_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_32_ = l_Lean_KVMap_find(v_data_30_, v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_42_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_42_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_42_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_42_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
if (lean_obj_tag(v_val_33_) == 5)
{
lean_object* v_v_37_; lean_object* v___x_39_; 
v_v_37_ = lean_ctor_get(v_val_33_, 0);
lean_inc(v_v_37_);
lean_dec_ref(v_val_33_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v_v_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_v_37_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
else
{
lean_object* v___x_41_; 
lean_del_object(v___x_35_);
lean_dec(v_val_33_);
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v___x_32_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object* v_e_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_getRecAppSyntax_x3f(v_e_45_);
lean_dec_ref(v_e_45_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object* v_d_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_49_ = l_Lean_KVMap_contains(v_d_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object* v_d_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_MData_isRecApp(v_d_50_);
lean_dec(v_d_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object* v_e_53_){
_start:
{
if (lean_obj_tag(v_e_53_) == 10)
{
lean_object* v_data_54_; uint8_t v___x_55_; 
v_data_54_ = lean_ctor_get(v_e_53_, 0);
v___x_55_ = l_Lean_MData_isRecApp(v_data_54_);
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object* v_e_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_hasRecAppSyntax(v_e_57_);
lean_dec_ref(v_e_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_RecAppSyntax(builtin);
}
#ifdef __cplusplus
}
#endif
