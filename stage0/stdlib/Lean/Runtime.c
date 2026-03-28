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
lean_object* lean_libuv_version(lean_object*);
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object*);
static lean_once_cell_t l_Lean_closureMaxArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_closureMaxArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_closureMaxArgs;
static lean_once_cell_t l_Lean_maxSmallNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_maxSmallNat___closed__0;
LEAN_EXPORT lean_object* l_Lean_maxSmallNat;
static lean_once_cell_t l_Lean_libUVVersion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_libUVVersion___closed__0;
LEAN_EXPORT lean_object* l_Lean_libUVVersion;
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
LEAN_EXPORT lean_object* l_Lean_libUVVersionFn___boxed(lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_libuv_version(v_a_00___x40___internal___hyg_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_closure_max_args(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_closureMaxArgs(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_closureMaxArgs___closed__0, &l_Lean_closureMaxArgs___closed__0_once, _init_l_Lean_closureMaxArgs___closed__0);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_maxSmallNat___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_max_small_nat(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_maxSmallNat(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_maxSmallNat___closed__0, &l_Lean_maxSmallNat___closed__0_once, _init_l_Lean_maxSmallNat___closed__0);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_libUVVersion___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_libuv_version(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_libUVVersion(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_libUVVersion___closed__0, &l_Lean_libUVVersion___closed__0_once, _init_l_Lean_libUVVersion___closed__0);
return v___x_18_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Runtime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
lean_mark_persistent(l_Lean_closureMaxArgs);
l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
lean_mark_persistent(l_Lean_maxSmallNat);
l_Lean_libUVVersion = _init_l_Lean_libUVVersion();
lean_mark_persistent(l_Lean_libUVVersion);
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
