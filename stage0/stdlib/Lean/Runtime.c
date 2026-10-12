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
lean_object* lean_get_max_ctor_num_objs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxCtorNumObjs___boxed(lean_object*);
static lean_once_cell_t l_Lean_maxCtorNumObjs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxCtorNumObjs___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxCtorNumObjs;
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
LEAN_EXPORT void l_Lean_closureMaxArgsFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_closure_max_args(v_a_00___x40___internal___hyg_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l_Lean_closureMaxArgsFn___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_closure_max_args(v_a_00___x40___internal___hyg_3_);
return v_res_4_;
}
}
LEAN_EXPORT void l_Lean_maxSmallNatFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_5_ = stack[0].m_obj;
lean_object* v_res_6_;
v_res_6_ = lean_max_small_nat(v_a_00___x40___internal___hyg_5_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_maxSmallNatFn___boxed(lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_max_small_nat(v_a_00___x40___internal___hyg_7_);
return v_res_8_;
}
}
LEAN_EXPORT void l_Lean_getMaxCtorNumObjs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_9_ = stack[0].m_obj;
lean_object* v_res_10_;
v_res_10_ = lean_get_max_ctor_num_objs(v_a_00___x40___internal___hyg_9_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorNumObjs___boxed(lean_object* v_a_00___x40___internal___hyg_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lean_get_max_ctor_num_objs(v_a_00___x40___internal___hyg_11_);
return v_res_12_;
}
}
static lean_object* _init_l_Lean_maxCtorNumObjs___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_get_max_ctor_num_objs(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_maxCtorNumObjs(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_maxCtorNumObjs___closed__0, &l_Lean_maxCtorNumObjs___closed__0_once, _init_l_Lean_maxCtorNumObjs___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_getMaxCtorScalarsSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_16_ = stack[0].m_obj;
lean_object* v_res_17_;
v_res_17_ = lean_get_max_ctor_scalars_size(v_a_00___x40___internal___hyg_16_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorScalarsSize___boxed(lean_object* v_a_00___x40___internal___hyg_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lean_get_max_ctor_scalars_size(v_a_00___x40___internal___hyg_18_);
return v_res_19_;
}
}
static lean_object* _init_l_Lean_maxCtorScalarsSize___closed__0(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_box(0);
v___x_21_ = lean_get_max_ctor_scalars_size(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_maxCtorScalarsSize(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&l_Lean_maxCtorScalarsSize___closed__0, &l_Lean_maxCtorScalarsSize___closed__0_once, _init_l_Lean_maxCtorScalarsSize___closed__0);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_getMaxCtorTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_23_ = stack[0].m_obj;
lean_object* v_res_24_;
v_res_24_ = lean_get_max_ctor_tag(v_a_00___x40___internal___hyg_23_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_getMaxCtorTag___boxed(lean_object* v_a_00___x40___internal___hyg_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lean_get_max_ctor_tag(v_a_00___x40___internal___hyg_25_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_maxCtorTag___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_get_max_ctor_tag(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_maxCtorTag(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&l_Lean_maxCtorTag___closed__0, &l_Lean_maxCtorTag___closed__0_once, _init_l_Lean_maxCtorTag___closed__0);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_getUSizeSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_30_ = stack[0].m_obj;
lean_object* v_res_31_;
v_res_31_ = lean_get_usize_size(v_a_00___x40___internal___hyg_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_getUSizeSize___boxed(lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_get_usize_size(v_a_00___x40___internal___hyg_32_);
return v_res_33_;
}
}
static lean_object* _init_l_Lean_usizeSize___closed__0(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_get_usize_size(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_usizeSize(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Lean_usizeSize___closed__0, &l_Lean_usizeSize___closed__0_once, _init_l_Lean_usizeSize___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lean_libUVVersionFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_37_ = stack[0].m_obj;
lean_object* v_res_38_;
v_res_38_ = lean_libuv_version(v_a_00___x40___internal___hyg_37_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object* v_a_00___x40___internal___hyg_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_libuv_version(v_a_00___x40___internal___hyg_39_);
return v_res_40_;
}
}
LEAN_EXPORT void l_Lean_openSSLVersionFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_41_ = stack[0].m_obj;
lean_object* v_res_42_;
v_res_42_ = lean_openssl_version(v_a_00___x40___internal___hyg_41_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_openSSLVersionFn___boxed(lean_object* v_a_00___x40___internal___hyg_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lean_openssl_version(v_a_00___x40___internal___hyg_43_);
return v_res_44_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_box(0);
v___x_46_ = lean_closure_max_args(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lean_closureMaxArgs___closed__0, &l_Lean_closureMaxArgs___closed__0_once, _init_l_Lean_closureMaxArgs___closed__0);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_maxSmallNat___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(0);
v___x_49_ = lean_max_small_nat(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_maxSmallNat(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Lean_maxSmallNat___closed__0, &l_Lean_maxSmallNat___closed__0_once, _init_l_Lean_maxSmallNat___closed__0);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_libUVVersion___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_libuv_version(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_libUVVersion(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Lean_libUVVersion___closed__0, &l_Lean_libUVVersion___closed__0_once, _init_l_Lean_libUVVersion___closed__0);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_openSSLVersion___closed__0(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_box(0);
v___x_55_ = lean_openssl_version(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_openSSLVersion(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Lean_openSSLVersion___closed__0, &l_Lean_openSSLVersion___closed__0_once, _init_l_Lean_openSSLVersion___closed__0);
return v___x_56_;
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
l_Lean_maxCtorNumObjs = _init_l_Lean_maxCtorNumObjs();
lean_mark_persistent(l_Lean_maxCtorNumObjs);
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
