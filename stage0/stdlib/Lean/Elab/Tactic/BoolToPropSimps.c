// Lean compiler output
// Module: Lean.Elab.Tactic.BoolToPropSimps
// Imports: Lean.Meta.Tactic.Simp.Attr
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
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_boolToPropSimps;
static lean_object* l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
static lean_object* l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_;
static lean_object* l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_(lean_object*);
LEAN_EXPORT lean_object* l_bool__to__prop;
static lean_object* l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
static lean_object* l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bool_to_prop", 12, 12);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp lemmas converting boolean expressions in terms of `decide` into propositional statements", 93, 93);
return x_1;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
x_3 = l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
x_4 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boolToPropSimps", 15, 15);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_;
x_3 = l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_;
x_4 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_2, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_ = _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_();
lean_mark_persistent(l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_);
l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_ = _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_();
lean_mark_persistent(l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_);
l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_ = _init_l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_();
lean_mark_persistent(l_initFn___closed__2____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_);
if (builtin) {res = l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_bool__to__prop = lean_io_result_get_value(res);
lean_mark_persistent(l_bool__to__prop);
lean_dec_ref(res);
}l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_ = _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_();
lean_mark_persistent(l_initFn___closed__0____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_);
l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_ = _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_();
lean_mark_persistent(l_initFn___closed__1____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_);
if (builtin) {res = l_initFn____x40_Lean_Elab_Tactic_BoolToPropSimps___hyg_29_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_boolToPropSimps = lean_io_result_get_value(res);
lean_mark_persistent(l_boolToPropSimps);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
