// Lean compiler output
// Module: init.lean.expr
// Imports: init.lean.level init.lean.kvmap
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_mk__dec__is__true___closed__1;
obj* l_lean_expr_dbg__to__string___boxed(obj*);
obj* l_lean_expr_mk__app(obj*, obj*);
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_mk__dec__is__true(obj*, obj*);
obj* l_lean_mk__dec__is__false(obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_lean_get__app__fn___main(obj*);
extern "C" obj* lean_expr_dbg_to_string(obj*);
obj* l_lean_expr__is__inhabited;
obj* l_lean_get__app__fn(obj*);
obj* l_lean_mk__bin__app(obj*, obj*, obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_expr_hash___boxed(obj*);
extern "C" usize lean_expr_hash(obj*);
obj* l_lean_mk__dec__is__false___closed__1;
obj* _init_l_lean_expr__is__inhabited() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean_expr_mk_app(x_0, x_3);
x_0 = x_8;
x_1 = x_5;
goto _start;
}
}
}
obj* l_lean_expr_mk__app(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_0, x_1);
return x_2;
}
}
obj* l_lean_expr_mk__capp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean_expr_mk_const(x_0, x_2);
x_4 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_3, x_1);
return x_4;
}
}
obj* l_lean_expr_hash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean_expr_hash(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* l_lean_expr_dbg__to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_expr_dbg_to_string(x_0);
return x_1;
}
}
obj* l_lean_get__app__fn___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 5:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_0 = x_1;
goto _start;
}
default:
{
return x_0;
}
}
}
}
obj* l_lean_get__app__fn(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_get__app__fn___main(x_0);
return x_1;
}
}
obj* l_lean_mk__bin__app(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean_expr_mk_app(x_0, x_1);
x_4 = lean_expr_mk_app(x_3, x_2);
return x_4;
}
}
obj* _init_l_lean_mk__dec__is__true___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("decidable");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("is_true");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean_expr_mk_const(x_5, x_0);
return x_6;
}
}
obj* l_lean_mk__dec__is__true(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_mk__dec__is__true___closed__1;
lean::inc(x_2);
x_4 = l_lean_mk__bin__app(x_2, x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_mk__dec__is__false___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("decidable");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("is_false");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean_expr_mk_const(x_5, x_0);
return x_6;
}
}
obj* l_lean_mk__dec__is__false(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_mk__dec__is__false___closed__1;
lean::inc(x_2);
x_4 = l_lean_mk__bin__app(x_2, x_0, x_1);
return x_4;
}
}
void initialize_init_lean_level();
void initialize_init_lean_kvmap();
static bool _G_initialized = false;
void initialize_init_lean_expr() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_level();
 initialize_init_lean_kvmap();
 l_lean_expr__is__inhabited = _init_l_lean_expr__is__inhabited();
 l_lean_mk__dec__is__true___closed__1 = _init_l_lean_mk__dec__is__true___closed__1();
 l_lean_mk__dec__is__false___closed__1 = _init_l_lean_mk__dec__is__false___closed__1();
}
