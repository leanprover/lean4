// Lean compiler output
// Module: Lean.Compiler.NeverExtractAttr
// Imports: Init Lean.Environment Lean.Attributes
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
lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3_(lean_object*);
extern lean_object* l_Lean_TagAttribute_Lean_Attributes___instance__5___closed__1;
lean_object* l_Lean_neverExtractAttr;
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2;
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3;
uint8_t lean_has_never_extract_attribute(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hasNeverExtractAttribute_visit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("neverExtract");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects.");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3;
x_4 = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_neverExtractAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Name_isInternal(x_2);
if (x_5 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_2 = x_6;
goto _start;
}
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = 1;
return x_8;
}
}
}
lean_object* l_Lean_hasNeverExtractAttribute_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_hasNeverExtractAttribute_visit(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t lean_has_never_extract_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_hasNeverExtractAttribute_visit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_never_extract_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_NeverExtractAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3____closed__4);
res = l_Lean_initFn____x40_Lean_Compiler_NeverExtractAttr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_neverExtractAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_neverExtractAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
