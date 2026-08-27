// Lean compiler output
// Module: Init.System.Platform
// Imports: public import Init.Data.Nat.Div.Basic public import Init.SimpLemmas import Init.Data.Nat.Basic import Init.Data.String.Bootstrap
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
uint8_t lean_system_platform_windows(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object*);
uint8_t lean_system_platform_osx(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object*);
uint8_t lean_system_platform_linux(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsLinux___boxed(lean_object*);
uint8_t lean_system_platform_emscripten(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object*);
static lean_once_cell_t l_System_Platform_isWindows___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isWindows___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isWindows;
static lean_once_cell_t l_System_Platform_isOSX___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isOSX___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isOSX;
static lean_once_cell_t l_System_Platform_isLinux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isLinux___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isLinux;
static lean_once_cell_t l_System_Platform_isEmscripten___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_Platform_isEmscripten___closed__0;
LEAN_EXPORT uint8_t l_System_Platform_isEmscripten;
lean_object* lean_system_platform_target(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object*);
static lean_once_cell_t l_System_Platform_target___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_Platform_target___closed__0;
LEAN_EXPORT lean_object* l_System_Platform_target;
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_Internal_getHardwareConcurrency___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
uint8_t v_res_3_; lean_object* v_r_4_; 
v_res_3_ = lean_system_platform_windows(v_a_00___x40___internal___hyg_2_);
v_r_4_ = lean_box(v_res_3_);
return v_r_4_;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object* v_a_00___x40___internal___hyg_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = lean_system_platform_osx(v_a_00___x40___internal___hyg_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getIsLinux___boxed(lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lean_system_platform_linux(v_a_00___x40___internal___hyg_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = lean_system_platform_emscripten(v_a_00___x40___internal___hyg_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
static uint8_t _init_l_System_Platform_isWindows___closed__0(void){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_box(0);
v___x_18_ = lean_system_platform_windows(v___x_17_);
return v___x_18_;
}
}
static uint8_t _init_l_System_Platform_isWindows(void){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_uint8_once(&l_System_Platform_isWindows___closed__0, &l_System_Platform_isWindows___closed__0_once, _init_l_System_Platform_isWindows___closed__0);
return v___x_19_;
}
}
static uint8_t _init_l_System_Platform_isOSX___closed__0(void){
_start:
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_box(0);
v___x_21_ = lean_system_platform_osx(v___x_20_);
return v___x_21_;
}
}
static uint8_t _init_l_System_Platform_isOSX(void){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_uint8_once(&l_System_Platform_isOSX___closed__0, &l_System_Platform_isOSX___closed__0_once, _init_l_System_Platform_isOSX___closed__0);
return v___x_22_;
}
}
static uint8_t _init_l_System_Platform_isLinux___closed__0(void){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_box(0);
v___x_24_ = lean_system_platform_linux(v___x_23_);
return v___x_24_;
}
}
static uint8_t _init_l_System_Platform_isLinux(void){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lean_uint8_once(&l_System_Platform_isLinux___closed__0, &l_System_Platform_isLinux___closed__0_once, _init_l_System_Platform_isLinux___closed__0);
return v___x_25_;
}
}
static uint8_t _init_l_System_Platform_isEmscripten___closed__0(void){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_box(0);
v___x_27_ = lean_system_platform_emscripten(v___x_26_);
return v___x_27_;
}
}
static uint8_t _init_l_System_Platform_isEmscripten(void){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = lean_uint8_once(&l_System_Platform_isEmscripten___closed__0, &l_System_Platform_isEmscripten___closed__0_once, _init_l_System_Platform_isEmscripten___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lean_system_platform_target(v_a_00___x40___internal___hyg_30_);
return v_res_31_;
}
}
static lean_object* _init_l_System_Platform_target___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_system_platform_target(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_System_Platform_target(void){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_System_Platform_target___closed__0, &l_System_Platform_target___closed__0_once, _init_l_System_Platform_target___closed__0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_System_Platform_Internal_getHardwareConcurrency___boxed(lean_object* v_a_00___x40___internal___hyg_36_){
_start:
{
uint32_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = lean_internal_get_hardware_concurrency(v_a_00___x40___internal___hyg_36_);
v_r_38_ = lean_box_uint32(v_res_37_);
return v_r_38_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
l_System_Platform_isLinux = _init_l_System_Platform_isLinux();
l_System_Platform_isEmscripten = _init_l_System_Platform_isEmscripten();
l_System_Platform_target = _init_l_System_Platform_target();
lean_mark_persistent(l_System_Platform_target);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_Platform(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Platform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_Platform(builtin);
}
#ifdef __cplusplus
}
#endif
