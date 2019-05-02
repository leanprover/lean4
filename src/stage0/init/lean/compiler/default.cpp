// Lean compiler output
// Module: init.lean.compiler.default
// Imports: init.lean.compiler.constfolding init.lean.compiler.ir init.lean.compiler.pushproj init.lean.compiler.elimdead init.lean.compiler.simpcase
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
obj* l_Lean_IR_test___closed__2;
namespace lean {
namespace ir {
obj* test_core(obj*, obj*);
}}
namespace lean {
namespace ir {
obj* decl_to_string_core(obj*);
}}
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_IO_println___at_Lean_IR_test___spec__1(obj*, obj*);
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l_Lean_IR_test___closed__1;
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_IO_print___at_Lean_IR_test___spec__2(obj*, obj*);
obj* l_Lean_IR_Decl_simpCase___main(obj*);
extern obj* l_IO_println___rarg___closed__1;
obj* l_Lean_IR_test___closed__3;
obj* l_IO_print___at_Lean_IR_test___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::ir::decl_to_string_core(x_0);
x_3 = lean_io_prim_put_str(x_2, x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_IO_println___at_Lean_IR_test___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_print___at_Lean_IR_test___spec__2(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = l_IO_println___rarg___closed__1;
x_9 = lean_io_prim_put_str(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_14 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_2);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
}
}
obj* _init_l_Lean_IR_test___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After push projections ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After elim dead locals ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After simplify case ===");
return x_0;
}
}
namespace lean {
namespace ir {
obj* test_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_IO_println___at_Lean_IR_test___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = l_Lean_IR_Decl_pushProj___main(x_0);
x_10 = l_Lean_IR_test___closed__1;
x_11 = l_IO_println___at_HasRepr_HasEval___spec__1(x_10, x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
x_12 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_14 = x_11;
} else {
 lean::inc(x_12);
 lean::dec(x_11);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_12);
lean::inc(x_9);
x_17 = l_IO_println___at_Lean_IR_test___spec__1(x_9, x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_20 = x_17;
} else {
 lean::inc(x_18);
 lean::dec(x_17);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_7);
lean::cnstr_set(x_21, 1, x_18);
x_22 = l_Lean_IR_Decl_elimDead___main(x_9);
x_23 = l_Lean_IR_test___closed__2;
x_24 = l_IO_println___at_HasRepr_HasEval___spec__1(x_23, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
x_25 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_27 = x_24;
} else {
 lean::inc(x_25);
 lean::dec(x_24);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_7);
lean::cnstr_set(x_28, 1, x_25);
lean::inc(x_22);
x_30 = l_IO_println___at_Lean_IR_test___spec__1(x_22, x_28);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_31);
x_35 = l_Lean_IR_Decl_simpCase___main(x_22);
x_36 = l_Lean_IR_test___closed__3;
x_37 = l_IO_println___at_HasRepr_HasEval___spec__1(x_36, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_40 = x_37;
} else {
 lean::inc(x_38);
 lean::dec(x_37);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_7);
lean::cnstr_set(x_41, 1, x_38);
x_42 = l_IO_println___at_Lean_IR_test___spec__1(x_35, x_41);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_35);
x_44 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
}
else
{
obj* x_51; obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_22);
x_51 = lean::cnstr_get(x_30, 0);
x_53 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_55 = x_30;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_30);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set(x_56, 1, x_53);
return x_56;
}
}
else
{
obj* x_58; obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_22);
x_58 = lean::cnstr_get(x_24, 0);
x_60 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_62 = x_24;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_24);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set(x_63, 1, x_60);
return x_63;
}
}
else
{
obj* x_65; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_9);
x_65 = lean::cnstr_get(x_17, 0);
x_67 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_69 = x_17;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_17);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_65);
lean::cnstr_set(x_70, 1, x_67);
return x_70;
}
}
else
{
obj* x_72; obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_9);
x_72 = lean::cnstr_get(x_11, 0);
x_74 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 x_76 = x_11;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_11);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_72);
lean::cnstr_set(x_77, 1, x_74);
return x_77;
}
}
else
{
obj* x_79; obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_0);
x_79 = lean::cnstr_get(x_3, 0);
x_81 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_83 = x_3;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_3);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_79);
lean::cnstr_set(x_84, 1, x_81);
return x_84;
}
}
}
}}
obj* initialize_init_lean_compiler_constfolding(obj*);
obj* initialize_init_lean_compiler_ir(obj*);
obj* initialize_init_lean_compiler_pushproj(obj*);
obj* initialize_init_lean_compiler_elimdead(obj*);
obj* initialize_init_lean_compiler_simpcase(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_constfolding(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_pushproj(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_elimdead(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_simpcase(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_test___closed__1 = _init_l_Lean_IR_test___closed__1();
lean::mark_persistent(l_Lean_IR_test___closed__1);
 l_Lean_IR_test___closed__2 = _init_l_Lean_IR_test___closed__2();
lean::mark_persistent(l_Lean_IR_test___closed__2);
 l_Lean_IR_test___closed__3 = _init_l_Lean_IR_test___closed__3();
lean::mark_persistent(l_Lean_IR_test___closed__3);
return w;
}
