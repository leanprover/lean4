// Lean compiler output
// Module: Lean.ToLevel
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
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToLevel;
LEAN_EXPORT lean_object* l_Lean_instToLevel__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ToLevel_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ToLevel_imax(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instToLevel(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToLevel__1(lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_Level_succ___override(v_inst_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_ToLevel_max(lean_object* v_inst_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Level_max___override(v_inst_4_, v_inst_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_ToLevel_imax(lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Level_imax___override(v_inst_7_, v_inst_8_);
return v___x_9_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ToLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToLevel = _init_l_Lean_instToLevel();
lean_mark_persistent(l_Lean_instToLevel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ToLevel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ToLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ToLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ToLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ToLevel(builtin);
}
#ifdef __cplusplus
}
#endif
