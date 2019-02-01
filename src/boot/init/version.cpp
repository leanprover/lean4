// Lean compiler output
// Module: init.version
// Imports: init.data.nat.basic init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s11_is__release_s7___boxed;
obj* _l_s4_lean_s7_version;
unsigned char _l_s4_lean_s11_is__release;
obj* _l_s4_lean_s22_special__version__desc;
obj* _l_s4_lean_s7_githash;
obj* _init__l_s4_lean_s7_version() {
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = lean::mk_nat_obj(3u);
x_1 = lean::mk_nat_obj(1u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init__l_s4_lean_s7_githash() {
{
obj* x_0; 
x_0 = lean::mk_string("6e8f8a8cdc4fadd6c3dab251e8a30df824471616");
return x_0;
}
}
unsigned char _init__l_s4_lean_s11_is__release() {
{
unsigned char x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init__l_s4_lean_s11_is__release_s7___boxed() {
{
unsigned char x_0; obj* x_1; 
x_0 = _l_s4_lean_s11_is__release;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s22_special__version__desc() {
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_version() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_s4_lean_s7_version = _init__l_s4_lean_s7_version();
 _l_s4_lean_s7_githash = _init__l_s4_lean_s7_githash();
 _l_s4_lean_s11_is__release = _init__l_s4_lean_s11_is__release();
 _l_s4_lean_s11_is__release_s7___boxed = _init__l_s4_lean_s11_is__release_s7___boxed();
 _l_s4_lean_s22_special__version__desc = _init__l_s4_lean_s22_special__version__desc();
}
