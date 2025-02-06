// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.AutoAttach
// Imports: Lean.Meta.Transform Lean.Meta.Match.MatcherApp.Basic Lean.Elab.Tactic.Simp
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
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_wfPreprocessSimpExtension;
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6;
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4_(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7;
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4;
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8;
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1;
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wf_preprocess", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WF", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wfPreprocessSimpExtension", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3;
x_2 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4;
x_3 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5;
x_4 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(not yet functional)", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2;
x_3 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8;
x_4 = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7;
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_AutoAttach(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__1);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__2);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__3);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__4);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__5);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__6);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__7);
l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8 = _init_l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8();
lean_mark_persistent(l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4____closed__8);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_AutoAttach___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_wfPreprocessSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_wfPreprocessSimpExtension);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
