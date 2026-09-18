// Lean compiler output
// Module: Lean.Runtime
// Imports: public import Init.Prelude
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
lean_object* lean_closure_max_args(lean_object*);
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object*);
lean_object* lean_max_small_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object*);
lean_object* lean_get_max_ctor_fields(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxCtorFields___boxed(lean_object*);
static lean_once_cell_t l_Lean_maxCtorFields___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxCtorFields;
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxCtorScalarsSize___boxed(lean_object*);
static lean_once_cell_t l_Lean_maxCtorScalarsSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxCtorScalarsSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxCtorScalarsSize;
lean_object* lean_get_max_ctor_tag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxCtorTag___boxed(lean_object*);
static lean_once_cell_t l_Lean_maxCtorTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxCtorTag___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxCtorTag;
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getUSizeSize___boxed(lean_object*);
static lean_once_cell_t l_Lean_usizeSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_usizeSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_usizeSize;
lean_object* lean_libuv_version(lean_object*);
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object*);
lean_object* lean_openssl_version(lean_object*);
LEAN_EXPORT lean_object* l_Lean_openSSLVersionFn___boxed(lean_object*);
static lean_once_cell_t l_Lean_closureMaxArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_closureMaxArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgs;
static lean_once_cell_t l_Lean_maxSmallNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxSmallNat___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxSmallNat;
static lean_once_cell_t l_Lean_libUVVersion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_libUVVersion___closed__0;
LEAN_EXPORT lean_object* l_Lean_libUVVersion;
static lean_once_cell_t l_Lean_openSSLVersion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_openSSLVersion___closed__0;
LEAN_EXPORT lean_object* l_Lean_openSSLVersion;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_closure_max_args(v_a_00___x40___internal___hyg_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object* v_a_00___x40___internal___hyg_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lean_max_small_nat(v_a_00___x40___internal___hyg_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorFields___boxed(lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_get_max_ctor_fields(v_a_00___x40___internal___hyg_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_maxCtorFields___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_get_max_ctor_fields(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_maxCtorFields(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_maxCtorFields___closed__0, &l_Lean_maxCtorFields___closed__0_once, _init_l_Lean_maxCtorFields___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorScalarsSize___boxed(lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_get_max_ctor_scalars_size(v_a_00___x40___internal___hyg_14_);
return v_res_15_;
}
}
static lean_object* _init_l_Lean_maxCtorScalarsSize___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_get_max_ctor_scalars_size(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_maxCtorScalarsSize(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_maxCtorScalarsSize___closed__0, &l_Lean_maxCtorScalarsSize___closed__0_once, _init_l_Lean_maxCtorScalarsSize___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorTag___boxed(lean_object* v_a_00___x40___internal___hyg_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_get_max_ctor_tag(v_a_00___x40___internal___hyg_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Lean_maxCtorTag___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_get_max_ctor_tag(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_maxCtorTag(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_maxCtorTag___closed__0, &l_Lean_maxCtorTag___closed__0_once, _init_l_Lean_maxCtorTag___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_getUSizeSize___boxed(lean_object* v_a_00___x40___internal___hyg_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_get_usize_size(v_a_00___x40___internal___hyg_26_);
return v_res_27_;
}
}
static lean_object* _init_l_Lean_usizeSize___closed__0(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_box(0);
v___x_29_ = lean_get_usize_size(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_usizeSize(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_usizeSize___closed__0, &l_Lean_usizeSize___closed__0_once, _init_l_Lean_usizeSize___closed__0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_libuv_version(v_a_00___x40___internal___hyg_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_openSSLVersionFn___boxed(lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_openssl_version(v_a_00___x40___internal___hyg_35_);
return v_res_36_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_closure_max_args(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Lean_closureMaxArgs___closed__0, &l_Lean_closureMaxArgs___closed__0_once, _init_l_Lean_closureMaxArgs___closed__0);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_maxSmallNat___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_box(0);
v___x_41_ = lean_max_small_nat(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_maxSmallNat(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Lean_maxSmallNat___closed__0, &l_Lean_maxSmallNat___closed__0_once, _init_l_Lean_maxSmallNat___closed__0);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_libUVVersion___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_libuv_version(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_libUVVersion(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Lean_libUVVersion___closed__0, &l_Lean_libUVVersion___closed__0_once, _init_l_Lean_libUVVersion___closed__0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_openSSLVersion___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_box(0);
v___x_47_ = lean_openssl_version(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_openSSLVersion(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Lean_openSSLVersion___closed__0, &l_Lean_openSSLVersion___closed__0_once, _init_l_Lean_openSSLVersion___closed__0);
return v___x_48_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_maxCtorFields = _init_l_Lean_maxCtorFields();
lean_mark_persistent(l_Lean_maxCtorFields);
l_Lean_maxCtorScalarsSize = _init_l_Lean_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_maxCtorScalarsSize);
l_Lean_maxCtorTag = _init_l_Lean_maxCtorTag();
lean_mark_persistent(l_Lean_maxCtorTag);
l_Lean_usizeSize = _init_l_Lean_usizeSize();
lean_mark_persistent(l_Lean_usizeSize);
l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
lean_mark_persistent(l_Lean_closureMaxArgs);
l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
lean_mark_persistent(l_Lean_maxSmallNat);
l_Lean_libUVVersion = _init_l_Lean_libUVVersion();
lean_mark_persistent(l_Lean_libUVVersion);
l_Lean_openSSLVersion = _init_l_Lean_openSSLVersion();
lean_mark_persistent(l_Lean_openSSLVersion);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Runtime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Runtime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Runtime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Runtime(builtin);
}
#ifdef __cplusplus
}
#endif
