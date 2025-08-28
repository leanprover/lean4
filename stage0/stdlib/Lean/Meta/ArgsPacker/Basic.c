// Lean compiler output
// Module: Lean.Meta.ArgsPacker.Basic
// Imports: Init.Data.Array.Basic
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
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedArgsPacker;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l_Lean_Meta_defaultArgsPacker____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ArgsPacker_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_defaultArgsPacker____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedArgsPacker() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_;
return x_1;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_ = _init_l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_();
lean_mark_persistent(l_Lean_Meta_defaultArgsPacker___closed__0____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_);
l_Lean_Meta_defaultArgsPacker____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_ = _init_l_Lean_Meta_defaultArgsPacker____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_();
lean_mark_persistent(l_Lean_Meta_defaultArgsPacker____x40_Lean_Meta_ArgsPacker_Basic_2887468181____hygCtx___hyg_20_);
l_Lean_Meta_instInhabitedArgsPacker = _init_l_Lean_Meta_instInhabitedArgsPacker();
lean_mark_persistent(l_Lean_Meta_instInhabitedArgsPacker);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
