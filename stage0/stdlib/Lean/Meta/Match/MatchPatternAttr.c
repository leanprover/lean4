// Lean compiler output
// Module: Lean.Meta.Match.MatchPatternAttr
// Imports: Init Lean.Attributes
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
extern lean_object* l_Lean_instInhabitedTagAttribute___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2;
lean_object* l_Lean_hasMatchPatternAttribute___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object*);
uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1;
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3;
lean_object* l_Lean_matchPatternAttr;
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
#define _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("matchPattern");\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1_end;\
}\
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2_end;\
}\
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)");\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3_end;\
}\
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed), 4, 0);\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4_end;\
}\
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4_end: ((void) 0);}
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3;
x_4 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
uint8_t lean_has_match_pattern_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_matchPatternAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_hasMatchPatternAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_match_pattern_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1);
_init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2);
_init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3);
_init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4);
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4);
res = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_matchPatternAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_matchPatternAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
