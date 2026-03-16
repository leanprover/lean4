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
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_recApp"};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 14, 43, 140, 165, 123, 61, 74)}};
static const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1 = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey = (const lean_object*)&l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecAppWithSyntax(lean_object* v_e_5_, lean_object* v_stx_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = l_Lean_KVMap_empty;
v___x_8_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_9_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_9_, 0, v_stx_6_);
v___x_10_ = l_Lean_KVMap_insert(v___x_7_, v___x_8_, v___x_9_);
v___x_11_ = l_Lean_mkMData(v___x_10_, v_e_5_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f(lean_object* v_e_12_){
_start:
{
if (lean_obj_tag(v_e_12_) == 10)
{
lean_object* v_data_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_data_13_ = lean_ctor_get(v_e_12_, 0);
v___x_14_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_15_ = l_Lean_KVMap_find(v_data_13_, v___x_14_);
if (lean_obj_tag(v___x_15_) == 1)
{
lean_object* v_val_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_25_; 
v_val_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_25_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_val_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
if (lean_obj_tag(v_val_16_) == 5)
{
lean_object* v_v_20_; lean_object* v___x_22_; 
v_v_20_ = lean_ctor_get(v_val_16_, 0);
lean_inc(v_v_20_);
lean_dec_ref(v_val_16_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v_v_20_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_v_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
else
{
lean_object* v___x_24_; 
lean_del_object(v___x_18_);
lean_dec(v_val_16_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
}
else
{
lean_object* v___x_26_; 
lean_dec(v___x_15_);
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRecAppSyntax_x3f___boxed(lean_object* v_e_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_getRecAppSyntax_x3f(v_e_28_);
lean_dec_ref(v_e_28_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_MData_isRecApp(lean_object* v_d_30_){
_start:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = ((lean_object*)(l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey));
v___x_32_ = l_Lean_KVMap_contains(v_d_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MData_isRecApp___boxed(lean_object* v_d_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Lean_MData_isRecApp(v_d_33_);
lean_dec(v_d_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Lean_hasRecAppSyntax(lean_object* v_e_36_){
_start:
{
if (lean_obj_tag(v_e_36_) == 10)
{
lean_object* v_data_37_; uint8_t v___x_38_; 
v_data_37_ = lean_ctor_get(v_e_36_, 0);
v___x_38_ = l_Lean_MData_isRecApp(v_data_37_);
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object* v_e_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_hasRecAppSyntax(v_e_40_);
lean_dec_ref(v_e_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
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
