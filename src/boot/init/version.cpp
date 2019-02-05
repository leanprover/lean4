// Lean compiler output
// Module: init.version
// Imports: init.data.nat.basic init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_version;
obj* l_lean_is__release___boxed;
unsigned char l_lean_is__release;
obj* l_lean_githash;
obj* l_lean_special__version__desc;
obj* _init_l_lean_version() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_nat_obj(4u);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init_l_lean_githash() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ff54bf337a650e15467693dec01949eb9ae853ce");
return x_0;
}
}
unsigned char _init_l_lean_is__release() {
_start:
{
unsigned char x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_lean_is__release___boxed() {
_start:
{
unsigned char x_0; obj* x_1; 
x_0 = l_lean_is__release;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_lean_special__version__desc() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
void initialize_init_data_nat_basic();
void initialize_init_data_string_basic();
static bool _G_initialized = false;
void initialize_init_version() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 initialize_init_data_string_basic();
 l_lean_version = _init_l_lean_version();
 l_lean_githash = _init_l_lean_githash();
 l_lean_is__release = _init_l_lean_is__release();
 l_lean_is__release___boxed = _init_l_lean_is__release___boxed();
 l_lean_special__version__desc = _init_l_lean_special__version__desc();
}
