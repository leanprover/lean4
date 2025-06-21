// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: Lean.Compiler.LCNF
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
static lean_object* l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_;
lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__3;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compile___lam__0___closed__1;
static lean_object* l_Lean_Compiler_compile___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__0;
static lean_object* l_Lean_Compiler_compile___lam__0___closed__2;
static lean_object* l_Lean_Compiler_compile___closed__1;
static lean_object* l_Lean_Compiler_compile___closed__0;
static lean_object* l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_;
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiling: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_compile___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_compile___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Compiler_compile___lam__0___closed__1;
x_7 = lean_array_to_list(x_1);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_7, x_8);
x_10 = l_Lean_MessageData_ofList(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Compiler_compile___lam__0___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_compile(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler new", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_compile___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__0___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_compile___closed__0;
x_8 = l_Lean_Compiler_compile___closed__2;
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lam__1), 5, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_box(1);
x_12 = l_Lean_Compiler_compile___lam__0___closed__2;
x_13 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed), 9, 6);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_7, x_5, x_13, x_14, x_2, x_3, x_4);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_compile___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_compile___closed__1;
x_2 = l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_compile___closed__1;
x_2 = l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stat", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_;
x_2 = l_Lean_Compiler_compile___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_compile___closed__2;
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_;
x_9 = lean_unbox(x_3);
x_10 = l_Lean_registerTraceClass(x_8, x_9, x_4, x_7);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* initialize_Lean_Compiler_LCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_compile___lam__0___closed__0 = _init_l_Lean_Compiler_compile___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_compile___lam__0___closed__0);
l_Lean_Compiler_compile___lam__0___closed__1 = _init_l_Lean_Compiler_compile___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___lam__0___closed__1);
l_Lean_Compiler_compile___lam__0___closed__2 = _init_l_Lean_Compiler_compile___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_compile___lam__0___closed__2);
l_Lean_Compiler_compile___lam__0___closed__3 = _init_l_Lean_Compiler_compile___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_compile___lam__0___closed__3);
l_Lean_Compiler_compile___closed__0 = _init_l_Lean_Compiler_compile___closed__0();
lean_mark_persistent(l_Lean_Compiler_compile___closed__0);
l_Lean_Compiler_compile___closed__1 = _init_l_Lean_Compiler_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___closed__1);
l_Lean_Compiler_compile___closed__2 = _init_l_Lean_Compiler_compile___closed__2();
lean_mark_persistent(l_Lean_Compiler_compile___closed__2);
l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__0____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__1____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__2____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__3____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__4____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__5____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__6____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__7____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__8____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__9____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__10____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__11____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__12____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__13____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__14____x40_Lean_Compiler_Main___hyg_89_);
l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_ = _init_l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_();
lean_mark_persistent(l_Lean_Compiler_initFn___closed__15____x40_Lean_Compiler_Main___hyg_89_);
if (builtin) {res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_89_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
