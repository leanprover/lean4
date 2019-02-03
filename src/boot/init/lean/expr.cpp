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
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s4_expr_s7_mk__app_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s19_expr__is__inhabited;
obj* _l_s4_lean_s4_expr_s7_mk__app(obj*, obj*);
obj* _l_s4_lean_s4_expr_s8_mk__capp(obj*, obj*);
obj* _init__l_s4_lean_s19_expr__is__inhabited(){
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s4_expr_s7_mk__app(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s4_expr_s7_mk__app_s9___spec__1(x_0, x_1);
return x_2;
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s4_expr_s7_mk__app_s9___spec__1(obj* x_0, obj* x_1){
_start:
{

if (lean::obj_tag(x_1) == 0)
{

lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
x_9 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s4_expr_s7_mk__app_s9___spec__1(x_8, x_5);
x_0 = x_8;
x_1 = x_5;
goto _start;
}
}
}
obj* _l_s4_lean_s4_expr_s8_mk__capp(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_cnstr(0, 0, 0);
;
x_3 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s4_expr_s7_mk__app_s9___spec__1(x_3, x_1);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_lean_s5_level();
void _l_initialize__l_s4_init_s4_lean_s5_kvmap();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s4_expr() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s5_level();
 _l_initialize__l_s4_init_s4_lean_s5_kvmap();
 _l_s4_lean_s19_expr__is__inhabited = _init__l_s4_lean_s19_expr__is__inhabited();
}
