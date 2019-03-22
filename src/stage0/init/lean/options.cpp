// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap init.io init.control.combinators init.data.tostring
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
obj* l___private_init_lean_options_1__initOptionDeclsRef(obj*);
obj* l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Options_HasEmptyc;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_Options_empty;
obj* l_Lean_registerOption___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_registerOption(obj*, obj*, obj*);
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
obj* l___private_init_lean_options_2__optionDeclsRef;
obj* l_Lean_getOptionDecls(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_registerOption___closed__2;
extern obj* l_IO_RefPointed;
obj* _init_l_Lean_Options_empty() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Options_HasEmptyc() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Options_empty;
return x_0;
}
}
obj* l___private_init_lean_options_1__initOptionDeclsRef(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::io_mk_ref(x_1, x_0);
return x_2;
}
}
obj* _init_l_Lean_registerOption___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid option declaration '");
return x_0;
}
}
obj* _init_l_Lean_registerOption___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', option already exists");
return x_0;
}
}
obj* l_Lean_registerOption(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_options_2__optionDeclsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_11; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
lean::inc(x_5);
x_11 = l_Lean_NameMap_contains___rarg(x_5, x_0);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
x_14 = l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_0, x_1);
x_15 = lean::io_ref_set(x_3, x_14, x_13);
return x_15;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_5);
lean::dec(x_1);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_0);
x_20 = l_Lean_registerOption___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = l_Lean_registerOption___closed__2;
x_24 = lean::string_append(x_21, x_23);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_7);
return x_25;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_4, 0);
x_30 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_32 = x_4;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_4);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_Lean_getOptionDecls(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l___private_init_lean_options_2__optionDeclsRef;
x_2 = lean::io_ref_get(x_1, x_0);
return x_2;
}
}
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_io(obj*);
obj* initialize_init_control_combinators(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_options(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
 l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean::mark_persistent(l_Lean_Options_empty);
 l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean::mark_persistent(l_Lean_Options_HasEmptyc);
w = l___private_init_lean_options_1__initOptionDeclsRef(w);
if (io_result_is_error(w)) return w;
 l___private_init_lean_options_2__optionDeclsRef = io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_options_2__optionDeclsRef);
 l_Lean_registerOption___closed__1 = _init_l_Lean_registerOption___closed__1();
lean::mark_persistent(l_Lean_registerOption___closed__1);
 l_Lean_registerOption___closed__2 = _init_l_Lean_registerOption___closed__2();
lean::mark_persistent(l_Lean_registerOption___closed__2);
return w;
}
