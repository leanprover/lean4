// Lean compiler output
// Module: Lean.LibrarySuggestions.Default
// Imports: public import Lean.LibrarySuggestions.SineQuaNon import all Lean.LibrarySuggestions.SineQuaNon
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
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static double l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
static double l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
lean_object* l_Lean_LibrarySuggestions_currentFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_Selector_intersperse(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(15u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
x_2 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
x_2 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static double _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; double x_10; lean_object* x_11; 
x_8 = l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
x_9 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_currentFile___boxed), 7, 0);
x_10 = l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_;
x_11 = l_Lean_LibrarySuggestions_Selector_intersperse(x_8, x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions___librarySuggestions_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Lean_LibrarySuggestions_SineQuaNon(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_SineQuaNon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_Default(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__0_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions___librarySuggestions___closed__1___boxed__const__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions___librarySuggestions___closed__1_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions___librarySuggestions___closed__2_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions___librarySuggestions___closed__3_00___x40_Lean_LibrarySuggestions_Default_2105568102____hygCtx___hyg_2_();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
