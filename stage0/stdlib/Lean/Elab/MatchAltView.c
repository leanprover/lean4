// Lean compiler output
// Module: Lean.Elab.MatchAltView
// Imports: Lean.Elab.Term
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedMatchAltView;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchAltView_ctorIdx(lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchAltView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
static lean_object* l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchAltView_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_MatchAltView_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_MatchAltView_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedMatchAltView() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_;
return x_1;
}
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MatchAltView(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_ = _init_l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_Elab_Term_defaultMatchAltView___closed__0____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_);
l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_ = _init_l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_Elab_Term_defaultMatchAltView___closed__1____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_);
l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_ = _init_l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_Elab_Term_defaultMatchAltView____x40_Lean_Elab_MatchAltView_2881784352____hygCtx___hyg_44_);
l_Lean_Elab_Term_instInhabitedMatchAltView = _init_l_Lean_Elab_Term_instInhabitedMatchAltView();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedMatchAltView);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
