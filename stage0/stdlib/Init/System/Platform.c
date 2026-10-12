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
LEAN_EXPORT void l_System_Platform_getIsWindows_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
uint8_t v_res_2_;
v_res_2_ = lean_system_platform_windows(v_a_00___x40___internal___hyg_1_);
stack->m_num = v_res_2_;
}
LEAN_EXPORT lean_object* l_System_Platform_getIsWindows___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = lean_system_platform_windows(v_a_00___x40___internal___hyg_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT void l_System_Platform_getIsOSX_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_6_ = stack[0].m_obj;
uint8_t v_res_7_;
v_res_7_ = lean_system_platform_osx(v_a_00___x40___internal___hyg_6_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_System_Platform_getIsOSX___boxed(lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lean_system_platform_osx(v_a_00___x40___internal___hyg_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT void l_System_Platform_getIsLinux_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_11_ = stack[0].m_obj;
uint8_t v_res_12_;
v_res_12_ = lean_system_platform_linux(v_a_00___x40___internal___hyg_11_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_System_Platform_getIsLinux___boxed(lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_system_platform_linux(v_a_00___x40___internal___hyg_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT void l_System_Platform_getIsEmscripten_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_16_ = stack[0].m_obj;
uint8_t v_res_17_;
v_res_17_ = lean_system_platform_emscripten(v_a_00___x40___internal___hyg_16_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_System_Platform_getIsEmscripten___boxed(lean_object* v_a_00___x40___internal___hyg_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = lean_system_platform_emscripten(v_a_00___x40___internal___hyg_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
static uint8_t _init_l_System_Platform_isWindows___closed__0(void){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_system_platform_windows(v___x_21_);
return v___x_22_;
}
}
static uint8_t _init_l_System_Platform_isWindows(void){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lean_uint8_once(&l_System_Platform_isWindows___closed__0, &l_System_Platform_isWindows___closed__0_once, _init_l_System_Platform_isWindows___closed__0);
return v___x_23_;
}
}
static uint8_t _init_l_System_Platform_isOSX___closed__0(void){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_box(0);
v___x_25_ = lean_system_platform_osx(v___x_24_);
return v___x_25_;
}
}
static uint8_t _init_l_System_Platform_isOSX(void){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_once(&l_System_Platform_isOSX___closed__0, &l_System_Platform_isOSX___closed__0_once, _init_l_System_Platform_isOSX___closed__0);
return v___x_26_;
}
}
static uint8_t _init_l_System_Platform_isLinux___closed__0(void){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_system_platform_linux(v___x_27_);
return v___x_28_;
}
}
static uint8_t _init_l_System_Platform_isLinux(void){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_uint8_once(&l_System_Platform_isLinux___closed__0, &l_System_Platform_isLinux___closed__0_once, _init_l_System_Platform_isLinux___closed__0);
return v___x_29_;
}
}
static uint8_t _init_l_System_Platform_isEmscripten___closed__0(void){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_box(0);
v___x_31_ = lean_system_platform_emscripten(v___x_30_);
return v___x_31_;
}
}
static uint8_t _init_l_System_Platform_isEmscripten(void){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = lean_uint8_once(&l_System_Platform_isEmscripten___closed__0, &l_System_Platform_isEmscripten___closed__0_once, _init_l_System_Platform_isEmscripten___closed__0);
return v___x_32_;
}
}
LEAN_EXPORT void l_System_Platform_getTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_33_ = stack[0].m_obj;
lean_object* v_res_34_;
v_res_34_ = lean_system_platform_target(v_a_00___x40___internal___hyg_33_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_System_Platform_getTarget___boxed(lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_system_platform_target(v_a_00___x40___internal___hyg_35_);
return v_res_36_;
}
}
static lean_object* _init_l_System_Platform_target___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_system_platform_target(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_System_Platform_target(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_System_Platform_target___closed__0, &l_System_Platform_target___closed__0_once, _init_l_System_Platform_target___closed__0);
return v___x_39_;
}
}
LEAN_EXPORT void l_System_Platform_Internal_getHardwareConcurrency_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_40_ = stack[0].m_obj;
uint32_t v_res_41_;
v_res_41_ = lean_internal_get_hardware_concurrency(v_a_00___x40___internal___hyg_40_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_System_Platform_Internal_getHardwareConcurrency___boxed(lean_object* v_a_00___x40___internal___hyg_42_){
_start:
{
uint32_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = lean_internal_get_hardware_concurrency(v_a_00___x40___internal___hyg_42_);
v_r_44_ = lean_box_uint32(v_res_43_);
return v_r_44_;
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
