// Lean compiler output
// Module: Lean.Elab.Tactic.BoolToPropSimps
// Imports: public import Lean.Meta.Tactic.Simp.Attr
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
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
static lean_object* l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_bool__to__prop;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* _init_l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bool_to_prop", 12, 12);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp lemmas converting boolean expressions in terms of `decide` into propositional statements", 93, 93);
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
x_3 = l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
x_4 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = _init_l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
lean_mark_persistent(l_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_);
l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = _init_l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
lean_mark_persistent(l_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_);
l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = _init_l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
lean_mark_persistent(l_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_);
if (builtin) {res = l_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_bool__to__prop = lean_io_result_get_value(res);
lean_mark_persistent(l_bool__to__prop);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
