// Lean compiler output
// Module: Init.Lean.Compiler.NeverExtractAttr
// Imports: Init.Lean.Environment Init.Lean.Attributes
#include "runtime/lean.h"
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
lean_object* l_Lean_neverExtractAttr;
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
lean_object* l_Lean_hasNeverExtractAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___closed__2;
lean_object* l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___boxed(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux(lean_object*, lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___lambda__1___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___closed__3;
uint8_t lean_has_never_extract_attribute(lean_object*, lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___closed__4;
uint8_t l_Lean_Name_isInternal___main(lean_object*);
lean_object* l_Lean_mkNeverExtractAttr(lean_object*);
lean_object* l_Lean_mkNeverExtractAttr___closed__1;
lean_object* l_Lean_mkNeverExtractAttr___lambda__1___closed__1;
lean_object* _init_l_Lean_mkNeverExtractAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_mkNeverExtractAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkNeverExtractAttr___lambda__1___closed__1;
return x_3;
}
}
lean_object* _init_l_Lean_mkNeverExtractAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("neverExtract");
return x_1;
}
}
lean_object* _init_l_Lean_mkNeverExtractAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNeverExtractAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkNeverExtractAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects.");
return x_1;
}
}
lean_object* _init_l_Lean_mkNeverExtractAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkNeverExtractAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_mkNeverExtractAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkNeverExtractAttr___closed__2;
x_3 = l_Lean_mkNeverExtractAttr___closed__3;
x_4 = l_Lean_mkNeverExtractAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_mkNeverExtractAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkNeverExtractAttr___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_neverExtractAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Name_isInternal___main(x_2);
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
lean_object* l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t lean_has_never_extract_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Compiler_NeverExtractAttr_1__hasNeverExtractAttributeAux___main(x_1, x_2);
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
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_NeverExtractAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkNeverExtractAttr___lambda__1___closed__1 = _init_l_Lean_mkNeverExtractAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_mkNeverExtractAttr___lambda__1___closed__1);
l_Lean_mkNeverExtractAttr___closed__1 = _init_l_Lean_mkNeverExtractAttr___closed__1();
lean_mark_persistent(l_Lean_mkNeverExtractAttr___closed__1);
l_Lean_mkNeverExtractAttr___closed__2 = _init_l_Lean_mkNeverExtractAttr___closed__2();
lean_mark_persistent(l_Lean_mkNeverExtractAttr___closed__2);
l_Lean_mkNeverExtractAttr___closed__3 = _init_l_Lean_mkNeverExtractAttr___closed__3();
lean_mark_persistent(l_Lean_mkNeverExtractAttr___closed__3);
l_Lean_mkNeverExtractAttr___closed__4 = _init_l_Lean_mkNeverExtractAttr___closed__4();
lean_mark_persistent(l_Lean_mkNeverExtractAttr___closed__4);
res = l_Lean_mkNeverExtractAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_neverExtractAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_neverExtractAttr);
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
