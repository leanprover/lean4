// Lean compiler output
// Module: init.lean.expr
// Imports: init.lean.level init.lean.kvmap
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_expr_mk__app(obj*, obj*);
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_expr__is__inhabited;
obj* l_lean_expr_mk__capp(obj*, obj*);
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
obj* l_lean_expr_mk__app(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_0, x_1);
return x_2;
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
x_8 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
x_0 = x_8;
x_1 = x_5;
goto _start;
}
}
}
obj* l_lean_expr_mk__capp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_3, x_1);
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
}
